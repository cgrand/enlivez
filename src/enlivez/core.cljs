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

(defprotocol Component
  (ensure! [c k] "Returns (creating it if necessary) the child component for k.")
  (delete! [c] "Deletes this component"))

(defn ensure-path! [component path]
  (reduce ensure! component path))

(defn delete-path! [component path]
  (some-> (reduce ensure! component path) delete!))

(def root-component nil)

(defn update-components!
  [delta]
  (doseq [path (sort-by (comp - count) (delta false))]
    (delete-path! root-component path))
  (doseq [path (sort-by count (delta true))]
    (ensure-path! root-component path)))

(defn meta-subscriber [conn]
  (let [cache (atom {:seeds [] :prepared-rules []})
        aprev-paths (atom #{})]
    (fn [{:keys [tx-data db-after]}]
      (when (some (fn [[e a]] (#{::rules ::seeds} a)) tx-data)
        (let [seeds (into #{} (mapcat (fn [[e a v]] v)) (d/datoms db-after :aevt ::seeds))
              rules (into #{} (mapcat (fn [[e a v]] v)) (d/datoms db-after :aevt ::rules))
              prepared-rules (impl/prepare-rules rules)]
          (reset! cache {:seeds seeds :prepared-rules prepared-rules})))
      (when-not *reentrant*
        (let [pending-txs
              (binding [*reentrant* []]
                (let [{:keys [seeds prepared-rules]} @cache
                      paths (`component-path
                              (impl/eval-prepared-rules (into (impl/make-db db-after) seeds) prepared-rules))
                      paths (into #{} (map first) paths)
                      prev-paths @aprev-paths
                      delta 
                      {true (into #{} (remove prev-paths) paths)
                       false (into #{} (remove paths) prev-paths)}]
                  (prn 'DELTA delta)
                  (reset! aprev-paths paths)
                  (update-components! delta))
                *reentrant*)]
          (doseq [tx pending-txs]
            (d/transact! conn tx)))))))

(defn- register-meta-subscriber! [conn]
  (d/listen! conn ::meta-subscriber (meta-subscriber conn)))

;; Datasource is only accessible through subscription
(def ^:private conn
  (doto (d/create-conn core-schema) register-meta-subscriber!))

#_(defn hijack-conn! [existing-conn]
   (.log js/console "NOPE43")
   (let [existing-db @existing-conn]
     (doto (into (:schema existing-db) core-schema)
       (->>
         (d/init-db (d/datoms existing-db :eavt))
         (d/reset-conn! existing-conn)))
     (register-meta-subscriber! existing-conn))
   (set! conn existing-conn))

(defprotocol RuleSet
  (collect-rules [t] "Returns a collection of rules.")
  (collect-deps [t] "Returns a collection of deps (as vars)."))

(extend-protocol RuleSet
  default
  (collect-rules [t] (mapcat ::expansion (vals t)))
  (collect-deps [t] (mapcat ::deps (vals t))))

(defprotocol Template
  #_(additional-schema [t] "Returns schema declarations that should augment the current db")
  (instantiate! [t mount!]))

(defn expr-component [ump!]
  (let [children (atom {})
        doms (atom #{})]
    (reify Component
      (ensure! [c v]
        (or (@children v)
          (let [child (reify Component
                        (delete! [c]
                          (let [doms (swap! doms disj v)]
                            (swap! children dissoc v)
                            (ump! (seq doms)))))]
            (swap! children assoc v child)
            (ump! (seq (swap! doms conj v)))
            child)))
      (delete! [c] nil))))

(defn for-component [child sort-child ump!]
  (let [children (atom {})
        doms (atom {})
        order (atom (sorted-set))]
    (reify Component
      (ensure! [c k]
        (or (@children k)
          (let [dom-child (instantiate! child
                            #(let [doms (swap! doms assoc k %)]
                               (->> @order (keep (comp doms second)) ump!)))
                sorter #_(some-> sort-child (instantiate! #(prn 'SORT %)))
                (reify Component
                  (ensure! [c sortk]
                    (->> (swap! order conj [sortk k]) (map second) (keep @doms) ump!)
                    (reify Component
                      (delete! [c]
                        (->> (swap! order disj [sortk k]) (map second) (keep @doms) ump!))))
                  (delete! [c]))
                bichild (reify Component
                          (ensure! [c k]
                            (case k
                              :dom dom-child
                              :sort sorter))
                          (delete! [c]
                            (let [doms (swap! doms dissoc k)]
                              (swap! children dissoc k)
                              (->> @order (keep (comp doms second)) ump!)
                              (delete! dom-child))))]
            (swap! children assoc k bichild)
            bichild)))
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

(defn state-component [state-map child ump!]
  (let [vk (volatile! nil)
        vchild (volatile! nil)]
    (reify Component
      (ensure! [c state-k]
        (or @vchild
          (do
            (transact-right-after! [(assoc state-map ::key state-k)])
            (vreset! vk state-k)
            (vreset! vchild (instantiate! child ump!)))))
      (delete! [c]
        (some-> @vchild delete!)
        (vreset! vchild nil)
        (when-some [state-k @vk]
          (transact-right-after! [[:db/retractEntity [::key state-k]]]))
        (vreset! vk nil)))))


(defn expr-template [rules deps retvar]
  (reify RuleSet
    (collect-rules [t] rules)
    (collect-deps [t] deps)
    Template
    (instantiate! [t mount!]
      (expr-component mount!))))

(defn for-template [activation
                    body-activation child
                    sort-activation sort-child
                    rule-vars rule-bodies
                    {:keys [rules deps]}]
  (let [[_ ppath & bound-vars] activation
        bound-vars (set bound-vars)
        qhead (cons (gensym "q") rule-vars)
        qrules (map #(cons qhead %) rule-bodies)
        ks (vec rule-vars ; TO REFINE
             #_(impl/keyvars rule-bodies (:rschema @conn) bound-vars))
        k (gensym "k")
        main-rule (list body-activation
                    activation
                    qhead
                    (list* 'call vector (conj ks k))
                    (list 'call conj ppath k :dom (second body-activation)))
        sort-rule (list sort-activation
                    activation
                    qhead
                    (list* 'call vector (conj ks k))
                    (list 'call conj ppath k :sort (second sort-activation)))]
    (reify RuleSet
      #_(additional-schema [t] (additional-schema child))
      (collect-rules [t]
        (list*
          main-rule
          sort-rule
          (list (list `component-path (second body-activation)) body-activation)
          (list (list `component-path (second sort-activation)) sort-activation)
          (concat
            qrules
            rules
            (collect-rules child)
            (collect-rules sort-child))))
      (collect-deps [t]
        (concat deps (collect-deps child) (collect-deps sort-child)))
      Template
      (instantiate! [t mount!]
        (for-component child sort-child mount!)))))

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

(defn state-template [state-map rules child]
  (reify RuleSet
    (collect-rules [t] (concat rules (collect-rules child)))
    (collect-deps [t] (collect-deps child))
    Template
    (instantiate! [t mount!] (state-component state-map child mount!))))

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
                (keep (fn [[k v :as kv]]
                        (cond
                          (not (sequential? v)) kv
                          (next v) kv ; apply str?
                          (seq v) [k (first v)]
                          :else nil)))
                x)]
    (not (sequential? x)) [x]
    (and (vector? x) (keyword? (first x)))
    [(into [(first x)] (mapcat simplify (rest x)))]
    :else (mapcat simplify x)))

(defn collect-all-rules 
  ([ruleset] (collect-all-rules (collect-rules ruleset) (collect-deps ruleset)))
  ([rules deps]
    (loop [rules (set rules) done-deps #{} deps (set deps)]
      (if (seq deps)
        (let [done-deps (into done-deps deps)]
          (recur
            (into rules (mapcat #(collect-rules @%)) deps)
            done-deps
            (into #{} (comp (mapcat #(collect-deps @%)) (remove done-deps)) deps)))
        rules))))

(defn handler [qname retname rules deps]
  (let [rules (collect-all-rules (reify RuleSet
                                   (collect-rules [t] rules)
                                   (collect-deps [t] deps)))]
    ; TODO : prepare rules
    (fn [args]
      (fn [e]
        (this-as this
          (let [tx-data (into []
                          (comp cat cat)
                          (get (impl/eval-rules
                                 (assoc (impl/make-db @conn) qname
                                   #{(list* e this args)}) rules)
                            retname))]
            (d/transact! conn tx-data)))))))

(defn trigger-handler
  "Runs the specified handler and returns its tx-data."
  [h & args]
  (let [[qname & expected-args] (first (::handler (::defhandler h)))
        rules (collect-all-rules h)
        call `call#
        activation `activation#
        call-rule `((~call ret#) (~activation ~@expected-args) (~qname ~@args ret#))
        rules (conj rules call-rule)]
    (when-not (= (count args) (count expected-args))
    (throw (ex-info (str "Not enough arguments passed to handler, expecting "
                      (count expected-args) " got " (count args))
             {:args args
              :expected-args expected-args})))
    (into []
     (comp cat cat)
     (get (impl/eval-rules
            (assoc (impl/make-db @conn) activation
              #{args}) rules)
       call))))

(def trigger-component
  (reify Component
    (ensure! [c [f & args]]
      (apply f args))
    (delete! [c])))

(defn mount [template-var elt & args]
  (let [activation (::activation (meta template-var))
        template @template-var
        seeds {(first activation) #{[[:dom] (vec args)]}}
        dom (r/atom nil)
        schema (let [db @conn]
                 (:rschema db)
                 #_(doto (into (:schema db) (additional-schema template))
                    (->> (d/init-db (d/datoms db :eavt)) (d/reset-conn! conn))))
        #_#_{root-eid -1} (:tempids (d/transact! conn [[:db/add -1 ::key []]]))
        [component txs] (binding [*reentrant* []]
                          [(instantiate! template #(reset! dom %)) *reentrant*])
        ; to pass schema or not to pass schema ?
        rules (collect-all-rules template)]
    (set! root-component
      (reify Component
        (ensure! [c k]
          (case k
            :dom component
            :trigger trigger-component))
        (delete! [c])))
    (d/transact! conn [{::seeds seeds ::rules rules :db/ident :root}])
    (doseq [tx txs] (d/transact! conn tx))
    (r/render [#(into [:<>] (simplify @dom))] elt)))

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
(defn io-trigger* [ident rules deps]
  (d/transact! conn
    [{::rules (collect-all-rules rules deps) :db/ident ident}]))


