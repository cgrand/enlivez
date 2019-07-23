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
              (f (pq db-after)))))))))

(defn call-with-db [db f this e]
  (let [tx (.call f this e db)]
    (if (map? tx) [tx] tx)))

(defn txing-handler [f]
  (fn [e]
    (this-as this
      (when-some [tx (f e this)]
        (d/transact! conn (if (map? tx) [tx] tx))))))

(defprotocol Template
  (additional-schema [t] "Returns schema declarations that should augment the current db")
  (query-tree [t whole-schema])
  (instantiate! [t mount! ks]))

(defprotocol Component
  (ensure! [c ks] "Returns the child component for (peek ks)")
  (delete! [c] "Deletes this component"))

(defn ensure-path! [component path]
  (reduce ensure! component (next (reductions conj [] path))))

(defn delete-path! [component path]
  (some-> (reduce get component path) delete!))

(defn- update-top [v f & args]
  (conj (pop v) (apply f (peek v) args)))

(defn for-component [child sort-f ump! flat-ks]
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
              (let [child (instantiate! child
                            #(let [doms (swap! doms assoc k %)]
                               (ump! (map (comp doms second) @ordered-ks)))
                            (update-top flat-ks into (conj k 1)))]
                (swap! children assoc k child)
                child)))))
      (delete! [c] nil))))

(defn fragment-component [dom children ump! flat-ks]
  (let [adom (atom dom)
        children
        (into []
          (map-indexed
            (fn [i [path child]]
              (instantiate! child #(ump! (swap! adom assoc-in path %))
                (update-top flat-ks conj i))))
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

(defn terminal-component [f ump! flat-ks]
  (reify
    ILookup
    (-lookup [c k] nil)
    Component
    (ensure! [c ks] (ump! (f (peek ks))) nil)
    (delete! [c] nil)))

(defn state-component [child ump! [parent-flat-k flat-k]]
  (d/transact! conn [[:db/add -1 ::key flat-k]
                     [:db/add [::key parent-flat-k] ::child -1]])
  (let [child (instantiate! child ump! [flat-k (conj flat-k '/)])]
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
            (d/transact! conn [[:db/retract [::key parent-flat-k] ::child [::key flat-k]]
                               [:db/retractEntity [::key flat-k]]])))))))

(defn for-template [q ks sort-ks sort-f child]
  (reify  Template
    (additional-schema [t] (additional-schema child))
    (query-tree [t whole-schema]
      {[q ks] {0 {[[] sort-ks] nil}
               1 (query-tree child  whole-schema)}})
    (instantiate! [t mount! ks]
      (for-component child sort-f mount! ks))))

(defn fragment-template [body children]
  (reify Template
    (additional-schema [t] (into {} (map additional-schema) (map peek children)))
    (query-tree [t whole-schema]
      (into {} (map-indexed (fn [i child] [i (query-tree child whole-schema)])) (map peek children)))
    (instantiate! [t mount! ks]
      (fragment-component body children mount! ks))))

(defn terminal-template [args f]
  (reify
    Template
    (additional-schema [t] {})
    (query-tree [t whole-schema]
      {[[] args] nil})
    (instantiate! [t mount! ks]
      (terminal-component f mount! ks))))

(defn state-template [entity-q child]
  (reify
    Template
    (additional-schema [t] {})
    (query-tree [t whole-schema]
      {[entity-q nil] (query-tree child whole-schema)})
    (instantiate! [t mount! ks]
      (state-component child mount! ks))))

(defn include-template [clauses child]
  (reify
    Template
    (additional-schema [t] {})
    (query-tree [t whole-schema]
      {[clauses nil] (query-tree child whole-schema)})
    (instantiate! [t mount! ks]
      (instantiate! child mount! ks))))

(declare ^::special for ^::special fragment ^::special terminal)

(defn simplify [x]
  (cond
    (not (sequential? x)) [x]
    (and (vector? x) (keyword? (first x)))
    [(into [(first x)] (mapcat simplify (rest x)))]
    :else (mapcat simplify x)))

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

(defn- flatten-hq
  "interim fn to map from query trees to hierarchical queries"
  [qt]
  (or
    (seq (clj/for [[k v] qt
                   q (flatten-hq v)]
           (cons (if (number? k) [nil k] k) q)))
    [()]))

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
        schema (let [db @conn]
                 (doto (into (:schema db) (additional-schema template))
                   (->> (d/init-db (d/datoms db :eavt)) (d/reset-conn! conn))))
        {root-eid -1} (:tempids (d/transact! conn [[:db/add -1 ::key []]]))
        component (instantiate! template #(reset! dom %) [[] []])
        update! (fn [delta]
                  (doseq [path delta
                          :let [upsert (peek path)
                                path (pop path)
                                f (if upsert ensure-path! delete-path!)]]
                    (f component path)))
        subscriptions (vec (mapcat #(subscription % update!) (flatten-hq (query-tree template schema))))]
    (d/transact! conn subscriptions)
    (r/render [#(first (simplify @dom))] elt)))

;; Sorting

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

;; IO
(defn io-trigger*
  ([q binding send]
    (io-trigger* q binding send (constantly nil)))
  ([q binding send stop]
    (let [tx! #(d/transact! conn %)]
      (tx!
        (subscription [[q binding] [[] []]]
          (fn [delta]
            (doseq [[tuple _ addition] delta]
              (if addition
                (apply send tuple)
                (apply stop tuple)))))))))