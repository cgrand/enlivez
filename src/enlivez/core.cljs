(ns enlivez.core
  (:require-macros enlivez.core)
  (:refer-clojure :exclude [for])
  (:require
    [clojure.core :as clj]
    [datascript.core :as d]
    [enlivez.q :as q]
    [reagent.core :as r]))

; https://github.com/tonsky/datascript/wiki/Tips-&-tricks#editing-the-schema

#_(def ^:private rules-registry (atom {}))

;; *reentrant* doubles as a cache for newly allocated state eids
(def ^:private ^:dynamic *reentrant* nil)

;; Datasource is only accessible through subscription
(def ^:private conn
  (doto (d/create-conn {::child {:db/valueType :db.type/ref
                                 :db/isComponent true
                                 :db/cardinality :db.cardinality/many}
                        ::key {:db/unique :db.unique/identity}})
    (d/listen! ::meta-subscriber
      (fn [{:keys [tx-data db-after]}]
        (when-not *reentrant*
          (binding [*reentrant* {}]
            (doseq [[eid q f pq] (d/q '[:find ?eid ?q ?f ?pq :where [?eid ::live-query ?q] [?eid ::prepared-live-query ?pq] [?eid ::handler ?f]] db-after)]
              #_(prn 'RUNNING q)
              (f (pq db-after)))))))))

(defn call-with-db [db f this e]
  (let [tx (.call f this e db)]
    (if (map? tx) [tx] tx)))

(defn txing-handler [f]
  (fn [e]
    (this-as this
      (when-some [tx (.call f this e)]
        (d/transact! conn (if (map? tx) [tx] tx))))))

(defprotocol Component
  (ensure! [c ks] "Returns the child component for (peek ks)")
  (delete! [c] "Deletes this component"))

(defn ensure-path! [component path]
  (reduce ensure! component (next (reductions conj [] path))))

(defn delete-path! [component path]
  (some-> (reduce get component path) delete!))

(defn for-component [child sort-f ump! parent-state-eid flat-ks]
  (let [children (atom {})
        sort-ks (atom {})
        ordered-ks (atom nil)
        _ (reset! ordered-ks
            (sorted-set-by
              #(try
                (compare %1 %2)
                (catch :default e
                  (let [[sort-k k] %1]
                    (if (= (@sort-ks k) sort-k) ; existing key
                      1 -1))))))
        doms (atom {})
        delete-child
        (fn [k]
          (let [sort-k (@sort-ks k)
                ord (swap! ordered-ks disj [sort-k k])]
            (swap! sort-ks dissoc k)
            (swap! children dissoc k)
            (swap! doms dissoc k)
            (ump! (map (comp @doms second) ord))))
        child-component
        (fn [child-k child]
          (reify
            ILookup
            (-lookup [c k]
              (let [[dir] k]
                (case dir
                  ;; when switching sort order in between the ordered-ks are a mixed bag
                  0 (reify Component
                      (ensure! [c ks]
                        (let [sort-args (peek ks)
                              sort-k (sort-f sort-args)
                              prev-sort-k (@sort-ks child-k)
                              ord (swap! ordered-ks
                                    #(-> %
                                       (disj [prev-sort-k child-k])
                                       (conj [sort-k child-k])))]
                          (swap! sort-ks assoc child-k sort-k)
                          (ump! (map (comp @doms second) ord)))
                        nil)
                      (delete! [c]
                        (delete-child child-k)
                        (delete! child)))
                  1 child)))
            Component
            (ensure! [c ks]
              (get c (peek ks)))
            (delete! [c] nil)))]
    (reify
      ILookup
      (-lookup [c k]
        (some->> (@children k) (child-component k)))
      Component
      (ensure! [c ks]
        (let [k (peek ks)]
          (child-component k
            (or (@children k)
              (let [child (child
                            #(let [doms (swap! doms assoc k %)]
                               (ump! (map (comp doms second) @ordered-ks)))
                            parent-state-eid (conj (into flat-ks k) 1))]
                (swap! children assoc k child)
                child)))))
      (delete! [c] nil))))

(defn fragment-component [dom children ump! parent-state-eid flat-ks]
  (let [adom (atom dom)
        children
        (into []
          (map-indexed
            (fn [i [path child]]
              (child #(ump! (swap! adom assoc-in path %)) parent-state-eid
                (conj flat-ks i))))
          children)]
    (ump! dom)
    (reify
      ILookup
      (-lookup [c k]
        (let [[i] k]
          (if (some? i)
            (nth children i)
            c)))
      Component
      (ensure! [c ks] (get c (peek ks)))
      (delete! [c] nil))))

(defn terminal-component [f ump! parent-state-eid flat-ks]
  (reify
    ILookup
    (-lookup [c k] nil)
    Component
    (ensure! [c ks] (ump! (f (peek ks))) nil)
    (delete! [c] nil)))

(defn state-component [child ump! parent-state-eid flat-ks]
  (d/transact! conn [[:db/add -1 ::key flat-ks]
                     [:db/add parent-state-eid ::child -1]])
  (let [child (child ump! [::key flat-ks] flat-ks)]
    (reify
      ILookup
      (-lookup [c k] (-lookup child k))
      Component
      (ensure! [c ks]
        (ensure! child ks))
      (delete! [c]
        (try
          (delete! child)
          (finally
            (d/transact! conn [[:db/retract parent-state-eid ::child [::key flat-ks]]
                               [:db/retractEntity [::key flat-ks]]])))))))

(defn for-template [q ks sort-ks sort-f child]
  (let [[qks child] child
        qks (cons (list [q ks] [[] 0] [[] sort-ks])
              (map #(list* [q ks] [[] 1] %) qks))]
    [qks #(for-component child sort-f %1 %2 %3)]))

(defn fragment-template [body children]
  (let [qks (clj/for [[i [path [qks]]] (map vector (range) children)
                  qk qks]
              (cons [[] i] qk))
        children (vec (clj/for [[path [qks f]] children]
                        [path f]))]
    [qks #(fragment-component body children %1 %2 %3)]))

(defn terminal-template [args f]
  [[[[[] args]]] #(terminal-component f %1 %2 %3)])

(defn state-template [entity-q child]
  (let [[qks child] child]
    [(map #(cons [entity-q nil] %) qks) #(state-component child %1 %2 %3)]))

(defn include-template [clauses child]
  (let [[qks child] child]
    [(map #(cons [clauses nil] %) qks) child]))

(declare ^::special for ^::special fragment ^::special terminal)

(defn simplify [x]
  (if (sequential? x)
    (if (keyword? (first x))
      [(into [(first x)] (mapcat simplify (rest x)))]
      (mapcat simplify x))
    [x]))

(q/register-fn `ensure-state-id
  (fn [db k]
    (or (*reentrant* k)
      (let [eid (if-some [datom (first (d/datoms db :avet ::key k))]
                  (.-e datom)
                  (-> conn
                    (d/transact! [[:db/add -1 ::key k]])
                    :tempids
                    (get -1)))]
        (set! *reentrant* (assoc *reentrant* k eid))
        eid))))

(defn- flatten-q
  "Flattens a hierarchical query to a pair [actual-query f] where f
   is a function to map a row to a path."
  [hq]
  (prn 'HQ hq)
  (let [[where find ks seg-fns]
        (reduce
          (fn [[where find ks seg-fns] [q k]]
            (let [q (if (= `ensure-state (first q))
                      (let [[_ ?sk eid clauses] q]
                        (list* [(cons 'vector ks) ?sk] [(list `ensure-state-id '$ ?sk) eid] clauses))
                      q)
                  seg-fn (cond
                           (nil? k) nil
                           (number? k) (constantly [k])
                           :else
                           (let [from (count find)
                                 to (+ from (count k))]
                             #(into [] (subvec % from to))))] ; https://clojure.atlassian.net/browse/CLJS-3092
              [(into where q)
               (into find (if (number? k) nil k))
               (into ks (if (number? k) [k] k))
               (cond-> seg-fns seg-fn (conj seg-fn))]))
          [[] [] [] []] hq)
        [find where]
        (if (seq find)
          [find where]
          (let [v (gensym "?true")]
            [[v] (into [(list '= true v)] where)]))]
    [find where
     (fn [row] (into [] (map #(% row)) seg-fns))]))

(defn subscription
  "Returns transaction data.
   hq is a hierarchical query, that is a collection of pairs [q k]  where q is
   a sequence of datascript clauses and k is a collection of variables.
   A hierarchical query behaves likes the conjuctions of its queries and returns,
   for each tuple of the result set, a path. Each segment of this path correspond
   to the instanciation of the k components of hq.
   f is a functions that receives changes, when the db change, to hq result paths.
   This changes are represented by a set of vectors, each vector being a path with
   an additional top item: a boolean, true for addition, false for deletion.
   Upon transaction of the subscription, f receives a first delta (positive only) representing the current state."
  [hq f]
  (let [[find where path-fn] (flatten-q hq)]
    [{::live-query (concat [:find] find [:where] where)
      ::prepared-live-query (q/prepare-query find where)
      ::hierarchical-query hq
      ::handler
      (let [aprev-rows (atom #{})]
        (fn [rows]
          (let [prev-rows @aprev-rows
                ; I could also use a flat sorted map with the right order
                paths+ (into {}
                         (comp
                           (remove prev-rows)
                           (map path-fn)
                           (map (fn [path] [(pop path) path])))
                         rows)
                paths- (into #{}
                         (comp
                         (remove rows)
                           (map path-fn)
                           (keep (fn [path]
                                   (let [k (pop path)]
                                     (when-not (contains? paths+ k) (conj k false))))))
                         prev-rows)
                delta (into paths- (map (fn [[_ path]] (conj path true))) paths+)]
            (reset! aprev-rows rows)
            (when (not= #{} delta)
              #_(prn 'Q q)
              (prn 'DELTA delta)
              (f delta)))))}]))

(defn mount [template elt]
  (let [dom (r/atom nil)
        [qks instantiate!] template
        {root-eid -1} (:tempids (d/transact! conn [[:db/add -1 ::root true]]))
        component (instantiate! #(reset! dom %) root-eid [])
        update! (fn [delta]
                  (doseq [path delta
                          :let [upsert (peek path)
                                path (pop path)
                                f (if upsert ensure-path! delete-path!)]]
                    (f component path)))
        subscriptions (vec (mapcat #(subscription % update!) qks))]
    (d/transact! conn subscriptions)
    (r/render [#(first (simplify @dom))] elt)))

(defprotocol ISortKey
 (toggle [k])
 (asc [k]))

(declare desc)

(defrecord Desc [x]
 ISortKey
 (toggle [_] x)
 (asc [_] x)
 IComparable
 (-compare [a b]
   (if (instance? Desc b)
     (- (compare x (.-x b)))
     (throw (ex-info "Can't compare." {:a a :b b}))))
 IFn ; to wrap keywords
 (-invoke [_ a] (desc (x a))))

(defn desc [x]
  (Desc. (asc x)))

(extend-protocol ISortKey
  object
  (toggle [k] (Desc. k))
  (asc [k] k)
  number
  (toggle [k] (Desc. k))
  (asc [k] k)
  string
  (toggle [k] (Desc. k))
  (asc [k] k)
  boolean
  (toggle [k] (Desc. k))
  (asc [k] k)
  nil
  (toggle [k] nil)
  (asc [k] nil))

(defn push-or-toggle-sortk [sort-ks k]
  (let [basis (asc k)
        same-basis? (fn [x] (= basis (asc x)))
        fk (first sort-ks)]
    (if (same-basis? fk)
      (cons (toggle fk) (next sort-ks))
      (cons k (remove same-basis? sort-ks)))))

(defn sortk [x sort-ks]
  (into [] (map #(% x)) sort-ks))