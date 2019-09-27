(ns enlivez.core
  (:require-macros enlivez.core)
  (:refer-clojure :exclude [for])
  (:require
    [clojure.core :as clj]
    [datascript.core :as d]
    [enlivez.q :as q]
    [reagent.core :as r]
    [enlivez.impl.seminaive :as impl]))

; https://github.com/tonsky/datascript/wiki/Tips-&-tricks#editing-the-schema

#_(def ^:private rules-registry (atom {}))

;; *reentrant* doubles as a queue of pending tx
(def ^:private ^:dynamic *reentrant* nil)

(defn transact-right-after! [tx]
  (set! *reentrant* (conj *reentrant* tx)))

(def ^:private core-schema
  {::child {:db/valueType :db.type/ref
            :db/isComponent true
            :db/cardinality :db.cardinality/many}
   ::key {:db/unique :db.unique/identity}})

(defn- register-meta-subscriber! [conn]
  (d/listen! conn ::meta-subscriber
    (fn [{:keys [tx-data db-after]}]
      (when-not *reentrant*
        (let [pending-txs
              (binding [*reentrant* []]
                (doseq [[rules seeds f] (d/q '[:find ?rules ?seeds :where [?eid ::rules ?rules] [?eid ::seeds ?seeds] [?eid ::handler ?f]] db-after)]
                  (f (`ez/component-path
                       (impl/eval-rules (into (impl/make-db db-after) seeds) rules))))
                *reentrant*)]
          (doseq [tx pending-txs]
            (d/transact! conn tx)))))))

;; Datasource is only accessible through subscription
(def ^:private conn
  (doto (d/create-conn core-schema) register-meta-subscriber!))

(defn hijack-conn! [existing-conn]
  (.log js/console "NOPE43")
  (let [existing-db @existing-conn]
    (doto (into (:schema existing-db) core-schema)
      (->>
        (d/init-db (d/datoms existing-db :eavt))
        (d/reset-conn! existing-conn)))
    (register-meta-subscriber! existing-conn))
  (set! conn existing-conn))

(defn call-with-db [db f this e]
  (let [tx (.call f this e db)]
    (if (map? tx) [tx] tx)))

(defn txing-handler [f]
  (fn [e]
    (this-as this
      (when-some [tx (f e this @conn)]
        (d/transact! conn (if (map? tx) [tx] tx))))))

(defprotocol Template
  #_(additional-schema [t] "Returns schema declarations that should augment the current db")
  (collect-rules [t] "Returns a collection of rules.")
  (instantiate! [t mount!]))

#_(defn- qt-to-rules* [template parent-rule]
   (let [rulename (gensym 'rule)]
     (for [[[kve clauses] children] (query-tree template)]
       )))

#_(defn qt-to-rules [root-template]
   (let [rulename (gensym 'rule)]
     (for [[[kve clauses] children] (query-tree template)]
       ()
       )))


(defprotocol Component
  (ensure! [c k] "Returns (creating it if necessary) the child component for k.")
  (delete! [c] "Deletes this component"))

(defn ensure-path! [component path]
  (reduce ensure! component path))

(defn delete-path! [component path]
  (some-> (reduce get component path) delete!))

(defn- update-top [v f & args]
  (conj (pop v) (apply f (peek v) args)))

(defn for-component [child sort-f ump!]
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
                      (ensure! [c sort-args]
                        (let [sort-k (sort-f sort-args)
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
            (ensure! [c k]
              (get c k))
            (delete! [c] nil)))]
    (reify
      ILookup
      (-lookup [c k]
        (some->> (@children k) (child-component k)))
      Component
      (ensure! [c k]
        (child-component k
          (or (@children k)
            (let [child (instantiate! child
                          #(let [doms (swap! doms assoc k %)]
                             (ump! (map (comp doms second) @ordered-ks))))]
              (swap! children assoc k child)
              child))))
      (delete! [c] nil))))

(defn fragment-component [dom children ump!]
  (let [adom (atom dom)
        children
        (into []
          (map
            (fn [[path child]]
              (instantiate! child #(ump! (swap! adom assoc-in path %)))))
          children)]
    (ump! dom)
    (reify
      ILookup
      (-lookup [c i] (nth children i))
      Component
      (ensure! [c i] (nth children i))
      (delete! [c] nil))))

(defn terminal-component [f ump!]
  (reify
    ILookup
    (-lookup [c args] nil)
    Component
    (ensure! [c args] (ump! (f args)) nil)
    (delete! [c] nil)))

(defn state-component [state-f child ump! [parent-flat-k flat-k]]
  (transact-right-after! [{:db/id -1 ::key flat-k}
                          [:db/add [::key parent-flat-k] ::child -1]])
  (let [vchild (volatile! nil)]
    (reify
      ILookup
      (-lookup [c k] @vchild)
      Component
      (ensure! [c ks]
        (or @vchild
          (let [[eid & args] (peek ks)]
            (transact-right-after! [(assoc (state-f args) :db/id eid)])
            (vreset! vchild (instantiate! child ump!)))))
      (delete! [c]
        (try
          (delete! @vchild)
          (finally
            (d/transact! conn [[:db/retractEntity [::key flat-k]]])))))))

(defn for-template [activation body-activation
                    rule-vars rule-bodies
                    {:keys [rules deps]}
                    sort-ks sort-f
                    child]
  (let [[_ ppath & bound-vars] activation
        bound-vars (set bound-vars)
        qhead (cons (gensym "q") rule-vars)
        qrules (map #(cons qhead %) rule-bodies)
        ks (vec (impl/keyvars rule-bodies (:rschema @conn) bound-vars))
        k (gensym "k")
        path (second body-activation)
        main-rule (list body-activation
                    activation
                    qhead
                    (list* 'call vector (conj ks k))
                    (list 'call conj ppath k path))]
    (reify  Template
      #_(additional-schema [t] (additional-schema child))
      (collect-rules [t]
        (list*
          main-rule
          (list (list `component-path path) body-activation)
          (concat
            qrules
            rules
            (collect-rules child)))
        #_#_#_clauses
        ()
        {[q ks] {0 {[[] sort-ks] nil}
                 1 (query-tree child)}})
      (instantiate! [t mount!]
        (for-component child sort-f mount!)))))

(defn fragment-template [body children]
  (reify Template
    #_(additional-schema [t] (into {} (map additional-schema) (map peek children)))
    (collect-rules [t]
      (mapcat (fn [[path child [activation-head :as activation]]]
                (list* activation
                  (list (list `component-path (second activation-head)) activation-head)
                  (collect-rules child))) children))
    (instantiate! [t mount!]
      (fragment-component body children mount!))))

(defn terminal-template [rules f]
  (reify
    Template
    #_(additional-schema [t] {})
    (collect-rules [t] rules)
    (instantiate! [t mount!]
      (terminal-component f mount!))))

(defn state-template [eid args state-entity-f child]
  #_(reify
     Template
     #_(additional-schema [t] {})
     (collect-rules [t]
       {[#_[] (list `ensure-state eid)
         (into [eid] args)] (assoc
                              (query-tree child)
                              [[] nil] nil)})
     (instantiate! [t mount! ks]
       (state-component state-entity-f child mount! ks))))

(defn include-template [deps rules]
  (reify
    Template
    #_(additional-schema [t] {})
    (collect-rules [t] rules)
    (instantiate! [t mount!]
      #_(instantiate! child mount! ks))))

(declare ^::special for ^::special fragment ^::special terminal)

(defn simplify [x]
  (cond
    (map? x) [(into {}
                (remove (fn [[k v]]
                          (and (sequential? v) (empty? v))))
                x)]
    (not (sequential? x)) [x]
    (and (vector? x) (keyword? (first x)))
    [(into [(first x)] (mapcat simplify (rest x)))]
    :else (mapcat simplify x)))

(defn- gen-rules
  "interim fn to map from query trees to rules"
  ([qt] (gen-rules qt nil))
  ([qt [_ parent-path & parent-args :as parent-head]]
    (mapcat (fn [[k v]]
              (let [[q ks] (if (number? k) [nil k] k)
                    q (if (= `ensure-state (first q)) [q] q)
                    args (distinct (concat parent-args
                                     (filter #(and (symbol? %) (not= '_ %))
                                       (tree-seq seq? next
                                         (cons 'and q))))) ; not great with not
                    path-arg (gensym 'path)
                    rule-head (list* (gensym 'rule) path-arg args)
                    rule (if parent-head
                           (concat
                             (list* rule-head parent-head q)
                             [(list 'append parent-path ks path-arg)])
                           (concat
                             (cons rule-head q)
                             [(list 'append nil ks path-arg)]))]
                (cons rule (gen-rules v rule-head))))
      qt)))

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
  (let [[where find ks seg-fns]
        (reduce
          (fn [[where find ks seg-fns] [q k]]
            (let [is-state (= `ensure-state (first q))
                  q (if is-state
                      (let [[_ eid & clauses] q
                            ?sk (gensym "?sk")]
                        (into [[(cons 'vector ks) ?sk] [eid ::key ?sk]] clauses))
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
               (into ks (cond is-state [:/] (number? k) [k] :else k))
               (cond-> seg-fns seg-fn (conj seg-fn))]))
          [[] [] [] []] hq)
        [find where]
        (if (seq find)
          [find where]
          (let [v (gensym "?true")]
            [[v] (into [(list '= true v)] where)]))]
    [find where
     (fn [row] (into [] (map #(% row)) seg-fns))]))

(def ^:dynamic *print-delta* false)

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
  [rules seeds f]
  [{::rules rules
    ::seeds seeds
    ::handler
    (let [aprev-paths (atom #{})]
      (fn [paths]
        (let [prev-paths @aprev-paths
              delta 
              {true (into #{} (remove prev-paths) paths)
               false (into #{} (remove paths) prev-paths)}]
          (reset! aprev-paths paths)
          (when (not= #{} delta)
            (when *print-delta*
              (prn 'DELTA delta))
            (f delta)))))}])

(defn mount [template-var elt]
  (let [activation (::activation (meta template-var))
        template @template-var
        seeds {(first activation) #{[[]]}} ; crude seeding assuming root template has no arg
        dom (r/atom nil)
        schema (let [db @conn]
                 (:rschema db)
                 #_(doto (into (:schema db) (additional-schema template))
                    (->> (d/init-db (d/datoms db :eavt)) (d/reset-conn! conn))))
        {root-eid -1} (:tempids (d/transact! conn [[:db/add -1 ::key []]]))
        [root-component txs] (binding [*reentrant* []]
                               [(instantiate! template #(reset! dom %)) *reentrant*])
        update! (fn [delta]
                  (doseq [[added paths] delta
                          :let [f (if added ensure-path! delete-path!)]
                          path paths]
                    (f root-component path)))
        ; to pass schema or not to pass schema ?
        rules (collect-rules template)]
    (d/transact! conn (subscription rules seeds update!))
    (doseq [tx txs] (d/transact! conn tx))
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
      (throw (ex-info "TODO" {}))
#_      (tx!
         (subscription [[q binding] [[] []]]
           (fn [delta]
             (doseq [[tuple _ addition] delta]
               (if addition
                 (apply send tuple)
                 (apply stop tuple)))))))))

; should move to cljc
(defn collect-case-ruleset [{::keys [expansion deps] :as rule-value}]
  (loop [rule-set (set expansion) done #{} todo deps]
    (if (seq todo)
      (let [cases (mapcat (fn [dep] (vals @dep)) deps)]
        (recur
          (into rule-set (mapcat ::expansion) cases)
          (into done deps)
          (remove done (mapcat ::deps cases))))
      rule-set)))

(defn collect-ruleset [rule]
  (transduce (map collect-case-ruleset) into #{} (vals rule)))

(comment
  => (ez/deftemplate xoxo [] (for [(_ :user/name name)] [:h1 "hello" name]))
  => (`ez/component-path (impl/eval-rules {`xoxo #{[[] "You"]}} (ez/collect-rules xoxo)))
  #{([0 ["You"]])}
  
  => (def edb
       (-> (d/empty-db {})
         (d/db-with
           [[:db/add "1" :user/name "Lucy"]
            [:db/add "2" :user/name "Ethel"]
            [:db/add "3" :user/name "Fred"]])
         impl/make-db))
  => (ez/deftemplate xoxo [] (ez/for [(:user/name _ name)] [:h1 "hello" name]))
  => (`ez/component-path (impl/eval-rules (assoc edb `xoxo #{[[]]}) (ez/collect-rules xoxo)))
  #{([0])
    ([0 [1]])
    ([0 [1] 0])
    ([0 [1] 0 ["Lucy"]])
    ([0 [3]])
    ([0 [3] 0])
    ([0 [3] 0 ["Fred"]])
    ([0 [2]])
    ([0 [2] 0])
    ([0 [2] 0 ["Ethel"]])}
  
    => (def edb
       (-> (d/empty-db {:list/tail {:db/valueType :db.type/ref}})
         (d/db-with
           [[:db/add "1" :user/name "Lucy"]
            [:db/add "1" :list/tail "2"]
            [:db/add "2" :user/name "Ethel"]
            [:db/add "2" :list/tail "3"]
            [:db/add "3" :user/name "Fred"]])
         impl/make-db))
  => (ez/deftemplate reclist [root]
       [:h1 root]
       (ez/for [(:list/tail root tail)]
         (reclist tail)))
  => (`ez/component-path (impl/eval-rules (assoc edb `reclist #{[[]]}) (ez/collect-rules reclist)))
  => (`ez/component-path (impl/eval-rules (assoc edb `reclist #{[[] 1]}) (take 11 rules)))
#{([0])
  ([1])
  ([0 [1]]) ;h1
  ([1 []])
  ([1 [] 0])
  ([1 [] 0 0])
  ([1 [] 0 1])
  ([1 [] 0 0 [2]]) ;h1
  ([1 [] 0 1 []])
  ([1 [] 0 1 [] 0])
  ([1 [] 0 1 [] 0 0])
  ([1 [] 0 1 [] 0 1]) ;h1
  ([1 [] 0 1 [] 0 0 [3]])}
  
  
  
  => (ez/deftemplate tree [root]
       [:dt (ez/for [(:branch/name root name)] name)]
       [:dd
        [:dl
         (ez/for [(:branch/child root branch)]
           (tree branch))]]))

