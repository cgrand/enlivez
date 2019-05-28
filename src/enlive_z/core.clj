(ns enlive-z.core
  (:refer-clojure :exclude [for])
  (:require [clojure.core :as clj]
    [cljs.analyzer :as ana]
    [clojure.spec.alpha :as s]))

;; query maps syntax
(defn- reverse-lookup
  "Returns the direct keyword when the input keyord is reversed, else returns nil."
  [k]
  (when-some [[_ n] (when (keyword? k) (re-matches #"_(.*)" (name k)))]
    (keyword (namespace k) n)))

(defn unsugar-query-map [qmap]
  {:defaults (into {} (keep (fn [[k v]] (case v :or k nil))) qmap)
   ; expand :attrs and remove :or
   :qmap (into {}
           (mapcat
             (fn [[k v]]
               (cond
                 (= :or v) nil
                 (and (keyword? v) (= "attrs" (name v)))
                 (clj/for [x k]
                   [(keyword (or (namespace v) (namespace x)) (name x)) (symbol (name x))])
                 :else [[k v]])))
           qmap)})

(defn expand-query-map
  ; leveraging the spec is much work but it means the spec and this code
  ; may more easily drift away.
  [qmap]
  (let [{:keys [defaults qmap]} (unsugar-query-map qmap)
        eid (:db/id qmap (gensym '?id))
        qmap (dissoc qmap :db/id)]
    {:eid eid
     :clauses (vec
                (clj/for [[k v] qmap]
                  ; PONDER: outputting recursive clauses after all non-rec
                  (if (map? v) ; recursive expansion
                    (let [{:keys [clauses], attr-eid :eid} (expand-query-map v)]
                      (cons
                        (if-some [k (reverse-lookup k)]
                          [attr-eid k eid]
                          [eid k attr-eid])
                        clauses))
                    (if-some [k (reverse-lookup k)]
                        [v k eid]
                        (if-some [[_ default] (find defaults v)]
                          [(list 'get-else '$ eid k default) v]
                          [eid k v])))))}))

(defn expand-query [x]
  (let [x (if (map? x) [x] x)]
    (into [] (mapcat (fn [x] (if (map? x) (:clauses (expand-query-map x)) [x])) x))))

(defn question-var [x]
  (if (.startsWith (name x) "?")
    x
    (gensym (str "?" (name x)))))

;; keysets
(defn fresh-vars [expanded-q known-vars]
  (into {}
    (keep 
      (fn [x]
        (when (and (symbol? x) (not ('#{_ $} x))
                (or (:fresh (meta x)) (not (known-vars x))))
          [x (question-var x )])))
    ; assumes there are no extra datasources, and that a var can't appear in function
    ; position
    (tree-seq coll? #(if (seq? %) (next %) (seq %)) expanded-q)))

(defn- dnf "Returns a disjunctive normal form of the clause" [clause]
  (cond
    (vector? clause) [[clause]]
    ; expression-clause
    (seq? clause)
    (case (first clause)
      and (if-some [[clause & clauses] (next clause)]
            (clj/for [a (dnf clause) b (dnf (cons 'and clauses))]
              (concat a b))
            [[]])
      or (mapcat dnf (next clause))
      not (->> (dnf (cons 'and (next clause)))
            (reduce
              (fn [not-dnf conjunction]
                (clj/for [clause conjunction
                      conjunction' not-dnf]
                  (conj conjunction' (list 'not clause))))
              [[]])))
    :else (throw (ex-info (str "Unexpected clause " (pr-str clause)) {:clause clause}))))

(defn- scc
  "Returns the strongly connected components of a graph specified by its nodes
   and a successor function succs from node to nodes.
   The used algorithm is Tarjan's one."
  [nodes succs]
  (letfn [(sc [env node]
            ; env is a map from nodes to stack length or nil,
            ; nil means the node is known to belong to another SCC
            ; there are two special keys: ::stack for the current stack 
            ; and ::sccs for the current set of SCCs
            (if (contains? env node)
              env
              (let [stack (::stack env)
                    n (count stack)
                    env (assoc env node n ::stack (conj stack node))
                    env (reduce (fn [env succ]
                                  (let [env (sc env succ)]
                                    (assoc env node (min (or (env succ) n) (env node)))))
                          env (succs node))]
                (if (= n (env node)) ; no link below us in the stack, call it a SCC
                  (let [nodes (::stack env)
                        scc (set (take (- (count nodes) n) nodes))
                        ; clear all stack lengths for these nodes since this SCC is done
                        env (reduce #(assoc %1 %2 nil) env scc)]
                    (assoc env ::stack stack ::sccs (conj (::sccs env) scc)))
                  env))))]
    (::sccs (reduce sc {::stack () ::sccs #{}} nodes))))

; for a conjunction (of a DNF) we emit a graph of deps
(defn- deps [conjunction schema]
  (transduce (mapcat
              (fn self [clause]
                (if (seq? clause) 
                  (case (first clause)
                    ; emit nothing on not: imagine (not [?a :ident/attr :k])
                    not nil)
                  ; else must be a vector
                  (let [[e a v] (into clause '[_ _ _])
                        e (cond-> e (= '_ e) gensym)
                        v (cond-> v (= '_ v) gensym)]
                    (when-not (symbol? a)
                      (cond
                        (symbol? e)
                        (cond
                          (symbol? v)
                          (when (= :db.cardinality/one (get-in schema [a :db/cardinality] :db.cardinality/one))
                            [[e v]])
                
                          (get-in schema [a :db/unique]) [[:known v]])
              
                        (seq? e)
                        (case (first e)
                          get-else (let [v a
                                         [_ src e a default] e]
                                     (recur [e a v])))
                        :else :TODO))))))
    (completing
      (fn [succs [a b]]
        (update succs a (fnil conj []) b)))
    {} conjunction))

(defn- keyset [conjunction schema known-vars]
  (let [succs (-> (deps conjunction schema)
                (update :known (fnil into []) (keys known-vars)))
        sccs (scc (keys succs) succs)
        scc-of (into {}
                 (clj/for [scc sccs, var scc]
                   [var scc]))
        succs (into {}
                (map (fn [[a bs]]
                       (let [scc-a (scc-of a)]
                         [scc-a (into #{} (comp (remove scc-a) (map scc-of)) bs)])))
                succs)
        src-only (dissoc (reduce dissoc succs (mapcat val succs)) #{:known})]
    (keys src-only)))

(defn keyvars [expanded-q schema known-vars]
  ; in presence of many cycles the key may not be minimal
  (into #{} (comp (mapcat #(keyset % schema known-vars)) (map first)) (dnf (cons 'and expanded-q))))

(defn apply-aliases [x known-vars]
  (letfn [(walk [x]
            (cond
              (seq? x) (cons (first x) (map walk (next x)))
              (vector? x) (into [] (map walk) x)
              :else (known-vars x x)))]
    (walk x)))

;; state

(defn default-clauses [init qmap]
  (let [{:keys [defaults qmap]} (unsugar-query-map qmap)
        qmap (dissoc qmap :db/id)]
    ; no recursion? 
    ; support for recursive inits needs to be added on the transacting side upon instantiation too
    (clj/for [[k v] qmap]
      (if-some [v' (init k (defaults v))]
        (case [(symbol? v) (symbol? v')]
          [true true] [(list '= v v')]
          [true false] [(list 'ground v') v]
          [false true] [(list 'ground v) v']
          [(list '= v v')])
        (throw (ex-info (str "Init state can't satisfy state query; no default for " k) {:key k :init init :qmap qmap}))))))

;; hiccup-style template
(defn- handler [expr]
  `(txing-handler (fn [~'%]
                    (cljs.core/this-as ~'%this
                      ~expr))))

(defn- used-vars
  "vars must be a predicate"
  [expr known-vars]
  ; TODO make it right: it's an overestimate
  (set (filter known-vars (cons expr (tree-seq coll? seq expr)))))

(defn lift-expressions
  "Returns [expressions hollowed-x] where
   expressions is a sequence of [path expression] and hollowed-x is x where symbols and
   sequences have been replaced by nil."
  [known-vars x]
  (cond
    (associative? x)
    (reduce-kv (fn [[exprs x] k v]
                 (let [v (if (and (keyword? k) (.startsWith (name k) "on-"))
                           (handler v)
                           v)
                       [subexprs v] (lift-expressions known-vars v)]
                   [(into exprs
                      (clj/for [[path subexpr] subexprs]
                        [(cons k path) subexpr]))
                    (assoc x k v)]))
      [{} x] x)
    (or (symbol? x) (seq? x)) [{nil x} nil]
    :else [{} x]))

(defn terminal [env known-vars expr]
  (let [args (used-vars expr known-vars)]
    (fn [schema]
      `(terminal-template '[~@(map #(apply-aliases % known-vars) args)] (fn [[~@args]] ~expr)))))

(defn fragment* [env known-vars body]
  (let [[exprs body] (lift-expressions known-vars (vec body))
        children (clj/for [[paths expr] exprs]
                   [paths (let [{:keys [meta name]}
                                (when-some [x (and (seq? expr) (first expr))]
                                  (when (symbol? x) (some->> x (ana/resolve-var env))))]
                            (cond 
                              (::special meta)
                              (apply @(resolve name) env known-vars (next expr)) ; TODO inclusion
                              (::template meta)
                              (let [args (::template meta)
                                    clauses
                                    (map
                                      (fn [e arg]
                                        (cond
                                          (known-vars e)
                                          [(list 'identity (known-vars e)) arg]
                                          (seq? e)
                                          [(apply-aliases e known-vars) arg]
                                          :else
                                          [(list 'ground e) arg]))
                                      (next expr) args)]
                                (fn [schema] `(include-template '~clauses ~name)))
                              :else
                              (terminal env known-vars expr)))])]
    (fn [schema]
      `(fragment-template ~body
         [~@(clj/for [[path child] children] [`'~path (child schema)])]))))

(defn state [env known-vars init qmap body]
  ; TODO: init may have vars
  (let [{:keys [eid clauses]} (expand-query-map qmap)
        default-clauses (default-clauses init qmap)
        known-vars (into known-vars
                     (assoc (fresh-vars clauses {}) ; empty known-vars because :state must not filter
                       eid (question-var eid)))
        clauses (map #(apply-aliases % known-vars) clauses) ; TODO
        default-clauses (map #(apply-aliases % known-vars) default-clauses)
        child (fragment* env known-vars body)]
    (fn [schema]
      `(state-template '~init '(if-state ~(known-vars eid) ~clauses ~default-clauses) ~(child schema)))))

(s/def ::fragment-body
  (s/cat
    :options (s/* (s/cat :key keyword? :value any?))
    :body (s/* any?)))

(defmacro ^:private if-valid
  ([bindings+spec+value then] `(if-valid ~bindings+spec+value ~then nil))
  ([[bindings spec value] then else]
    `(let [conformed# (s/conform ~spec ~value)]
       (if (= ::s/invalid conformed#)
         ~else
         (let [~bindings conformed#]
           ~then)))))

(defn fragment [env known-vars & body]
  (if-valid [{:keys [body options]} ::fragment-body body]
    (let [{:keys [init] qmap :state} (into {} (map (juxt :key :value)) options)]
      (if qmap
        (state env known-vars (or init {}) qmap body)
        (fragment* env known-vars body)))
    (throw (ex-info "Invalid body" {:body body}))))

(defn for [env known-vars q & body]
  (let [q (expand-query q)
        vars (fresh-vars q known-vars)
        known-vars' (into known-vars vars)
        ?q (apply-aliases q known-vars')
        child (apply fragment env known-vars' body)]
    (fn [schema]
      (let [own-keys (map #(apply-aliases % known-vars') (keyvars q schema known-vars))] ; known-vars and not known-vars' because we care about vars that were previously known
        `(for-template '~?q '~own-keys
           ~(child schema))))))

(defmacro deftemplate [name args & body]
  (let [aliases (into {} (clj/for [arg args] [arg (question-var arg)]))
        template (apply fragment &env aliases body)
        schema {}]
    `(def ~(vary-meta name assoc ::template (mapv aliases args)) #_~args ~(template schema))))

#_(defmacro defrule [rulename args & clauses]
   (if (seq? args)
     `(do
        ~@(map (fn [args+clauses] `(defrule ~rulename ~@args+clauses)) (cons args clauses)))
     ))
