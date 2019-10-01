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
                (doseq [[rules seeds f] (d/q '[:find ?rules ?seeds ?f :where [?eid ::rules ?rules] [?eid ::seeds ?seeds] [?eid ::handler ?f]] db-after)]
                  (let [paths (`component-path
                                (impl/eval-rules (into (impl/make-db db-after) seeds) rules))]
                    (f paths)))
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

(defprotocol RuleSet
  (collect-rules [t] "Returns a collection of rules.")
  (collect-deps [t] "Returns a collection of deps (as vars)."))

(defprotocol Template
  #_(additional-schema [t] "Returns schema declarations that should augment the current db")
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
  (prn '>>>> 'ENSURE path)
  (reduce ensure! component path))

(defn delete-path! [component path]
  (prn '>>>> 'DELETE path)
  (some-> (ensure-path! component path) delete!))

(defn- update-top [v f & args]
  (conj (pop v) (apply f (peek v) args)))

(defn for-component [child sort-f ump!]
  (let [children (atom {})
        doms (atom {})]
    (reify Component
      (ensure! [c k]
        (or (@children k)
          (let [child (instantiate! child
                        #(let [doms (swap! doms assoc k %)]
                           (ump! (vals doms))))
                bound-child (reify Component
                              (ensure! [c k] (ensure! child k))
                              (delete! [c]
                                (let [doms (swap! doms dissoc k)]
                                  (swap! children dissoc k)
                                  (ump! (vals doms))
                                  (delete! child))))]
           (swap! children assoc k bound-child)
           child)))
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
    (reify Component
      (ensure! [c i] (nth children i))
      (delete! [c] nil))))

(defn terminal-component [f ump!]
  (reify Component
    (ensure! [c args] (ump! (f args)) nil)
    (delete! [c] nil)))

(defn state-component [state-f child ump! [parent-flat-k flat-k]]
  (transact-right-after! [{:db/id -1 ::key flat-k}
                          [:db/add [::key parent-flat-k] ::child -1]])
  (let [vchild (volatile! nil)]
    (reify Component
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
    (reify RuleSet
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
      (collect-deps [t]
        (concat deps (collect-deps child)))
      Template
      (instantiate! [t mount!]
        (for-component child sort-f mount!)))))

(defn fragment-template [body children]
  (reify RuleSet
    #_(additional-schema [t] (into {} (map additional-schema) (map peek children)))
    (collect-rules [t]
      (mapcat (fn [[path child [activation-head :as activation]]]
                (list* activation
                  (list (list `component-path (second activation-head)) activation-head)
                  (collect-rules child))) children))
    (collect-deps [t]
      (mapcat (fn [[_ child]] (collect-deps child)) children))
    Template
    (instantiate! [t mount!]
      (fragment-component body children mount!))))

(defn terminal-template [rules f]
  (reify RuleSet
    #_(additional-schema [t] {})
    (collect-rules [t] rules)
    (collect-deps [t] nil)
    Template
    (instantiate! [t mount!] (terminal-component f mount!))))

(defn state-template [eid args state-entity-f child]
  #_(reify Template
     #_(additional-schema [t] {})
     (collect-rules [t]
       {[#_[] (list `ensure-state eid)
         (into [eid] args)] (assoc
                              (query-tree child)
                              [[] nil] nil)})
     (instantiate! [t mount! ks]
       (state-component state-entity-f child mount! ks))))

(defn include-template [template-var deps rules]
  (reify RuleSet
    #_(additional-schema [t] {})
    (collect-rules [t] rules)
    (collect-deps [t] deps)
    Template
    (instantiate! [t mount!]
      (instantiate! @template-var mount!)
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
        (let [paths (into #{} (map first) paths)
              prev-paths @aprev-paths
              delta 
              {true (into #{} (remove prev-paths) paths)
               false (into #{} (remove paths) prev-paths)}]
          (reset! aprev-paths paths)
          (when (not= #{} delta)
            (when *print-delta*
              (prn 'DELTA delta))
            (f delta)))))}])

(defn collect-all-rules [ruleset]
  (loop [rules (set (collect-rules ruleset))
         done-deps #{}
         deps (set (collect-deps ruleset))]
    (if (seq deps)
      (let [done-deps (into done-deps deps)]
        (recur
          (into rules (mapcat #(collect-rules @%)) deps)
          done-deps
          (into #{} (comp (mapcat #(collect-deps @%)) (remove done-deps)) deps)))
      rules)))

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
                          :let [f (if added ensure-path! delete-path!)
                                order (if added count (comp - count))]
                          path (sort-by order paths)]
                    (f root-component path)))
        ; to pass schema or not to pass schema ?
        rules (collect-all-rules template)]
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

(comment
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
           (tree branch))]])
  
  => (require '[datascript.core :as d])
  (require'[enlivez.core :as ez])
  (require '[enlivez.impl.seminaive :as impl])
  (def edb
       (-> (d/empty-db {})
         (d/db-with
           [[:db/add "1" :user/name "Lucy"]
            [:db/add "2" :user/name "Ethel"]
            [:db/add "3" :user/name "Fred"]])
         impl/make-db))
  (ez/deftemplate xoxo [] (ez/for [(:user/name _ name)] [:h1 "hello" name]))
  (ez/mount #'xoxo (.-body js/document))
  )

