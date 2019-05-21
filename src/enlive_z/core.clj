(ns enlive-z.core
  (:require [cljs.analyzer :as ana]))

;; query maps syntax
(defn- reverse-lookup
  "Returns the direct keyword when the input keyord is reversed, else returns nil."
  [k]
  (when-some [[_ n] (when (keyword? k) (re-matches #"_(.*)" (name k)))]
    (keyword (namespace k) n)))

(defn expand-query-map
  ; leveraging the spec is much work but it means the spec and this code
  ; may more easily drift away.
  [qmap]
  (let [defaults (into {} (keep (fn [[k v]] (case v :or k nil))) qmap)
        ; expand :attrs and remove :or
        qmap (into {}
               (mapcat
                 (fn [[k v]]
                   (cond
                     (= :or v) nil
                     (and (keyword? v) (= "attrs" (name v)))
                     (for [x k]
                       [(keyword (or (namespace v) (namespace x)) (name x)) (symbol (name x))])
                     :else [[k v]])))
               qmap)
        eid (:db/id qmap (gensym '?id))
        qmap (dissoc qmap :db/id)]
    {:eid eid
     :clauses (for [[k v] qmap]
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
                      (if-some [[_ default] (find defaults k)]
                        [(list 'get-else eid k default) v]
                        [eid k v]))))}))

(defn expand-query [x]
  (let [x (if (map? x) [x] x)]
    (into [] (mapcat (fn [x] (if (map? x) (:clauses (expand-query-map x)) [x])) x))))

;; keysets
(defn implicit-vars [expanded-q] ; is this still needed? (except for _)
  (into #{}
    (filter #(and (symbol? %) (not= '_ %) #_(not (.startsWith (name %) "?"))))
    ; assumes there are no extra datasources, and that a var can't appear in function
    ; position
    (tree-seq coll? (fn [x] (cond-> (seq x) (seq? x) next)) expanded-q)))

(defn- dnf "Returns a disjunctive normal form of the clause" [clause]
  (cond
    (vector? clause) [[clause]]
    ; expression-clause
    (seq? clause)
    (case (first clause)
      and (if-some [[clause & clauses] (next clause)]
            (for [a (dnf clause) b (dnf (cons 'and clauses))]
              (concat a b))
            [[]])
      or (mapcat dnf (next clause))
      not (->> (dnf (cons 'and (next clause)))
            (reduce
              (fn [not-dnf conjunction]
                (for [clause conjunction
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
                  (let [[e a v] (into clause '[_ _ _])]
                    (when-not (or (= '_ e) (symbol? a) (= '_ v))
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
                (update :known (fnil into []) known-vars))
        sccs (scc (keys succs) succs)
        scc-of (into {}
                 (for [scc sccs, var scc]
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

(defn question-vars [x]
  (cond
    (seq? x) (cons (first x) (map question-vars (next x)))
    (vector? x) (into [] (map question-vars) x)
    (and (symbol? x) (not (.startsWith (name x) "?"))) (symbol (str "?" (name x)))
    :else x))

;; hiccup-style template
(defn lift-expressions
  "Returns [expressions hollowed-x] where
   expressions is a sequence of [path expression] and hollowed-x is x where symbols and
   sequences have been replaced by nil."
  [x]
  (cond
    (indexed? x)
    (reduce-kv (fn [[exprs x] k v]
                 (let [[subexprs v] (lift-expressions v)]
                   [(into exprs
                      (for [[path subexpr] subexprs]
                        [(cons k path) subexpr]))
                    (assoc x k v)]))
      [{} x] x)
    (or (symbol? x) (seq? x)) [{nil x} nil]
    :else [{} x]))

(defn- used-vars
  "vars must be a predicate"
  [expr known-vars]
  ; TODO make it right: it's an overestimate
  (set (filter known-vars (cons expr (flatten expr)))))

(declare special)

(defn terminal [env known-vars expr]
  (let [args (used-vars expr known-vars)]
    (fn [schema]
      `(terminal-template '[~@(map question-vars args)] (fn [[~@args]] ~expr)))))

(defn fragment [env known-vars & body]
  (let [[exprs body] (lift-expressions (vec body))
        children (for [[paths expr] exprs]
                   [paths (let [{:keys [meta name]}
                                (when-some [x (and (seq? expr) (first expr))]
                                  (when (symbol? x) (some->> x (ana/resolve-var env))))]
                            (if (::special meta)
                              (apply @(resolve name) env known-vars (next expr)) ; TODO inclusion
                              (terminal env known-vars expr)))])]
    (fn [schema]
      `(fragment-template ~body
         [~@(for [[path child] children] [`'~path (child schema)])]))))

(defn with [env known-vars q & body]
  (let [q (expand-query q)
        vars (implicit-vars q)
        ?q (question-vars q)
        child (apply fragment env (into known-vars vars) body)]
    (fn [schema]
      (let [own-keys (map question-vars (keyvars q schema known-vars))]
        `(with-template '~?q '~own-keys
           ~(child schema))))))

(defmacro deftemplate [name args & body]
  (let [template (apply fragment &env (set args) body)
        schema {}]
    `(def ~name ~(template schema))))

