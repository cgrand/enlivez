(ns enlivez.core
  (:refer-clojure :exclude [for])
  (:require [clojure.core :as clj]
    [cljs.analyzer :as ana]
    [clojure.spec.alpha :as s]))

(defprotocol Template
  (get-schema [_])
  (emit-cljs [_ schema]))

;; query maps syntax
(defn- reverse-lookup
  "Returns the direct keyword when the input keyword is reversed, else returns nil."
  [k]
  (when-some [[_ n] (when (keyword? k) (re-matches #"_(.*)" (name k)))]
    (keyword (namespace k) n)))

(defn unsugar-query-map [env qmap]
  {:defaults (into {}
               (keep
                 (fn [[k v]]
                   (cond
                     (and (= :or v) (map? k)) k ; is a map but map conjing is a thing
                     (symbol? k) [(symbol (name k)) v] ; auto keyword
                     :else nil)))
               qmap)
   ; expand :attrs, remove :or, auto keywords
   :qmap (into {}
           (keep
             (fn [[k v]]
               (cond
                 (and (= :or v) (map? k)) nil
                 (symbol? k)
                 (let [ns (some->>
                            (when-some [ns (namespace k)]
                              (or (ana/resolve-ns-alias env ns nil) (ana/resolve-macro-ns-alias env ns)))
                            name)]
                   [(keyword (or ns (name (ns-name *ns*))) (name k)) (symbol (name k))]) ; auto keyword
                 (and (keyword? v) (= "attrs" (name v)))
                 (into {}
                   (clj/for [x k]
                     [(keyword (or (namespace x) (namespace v)) (name x)) (symbol (name x))]))
                 :else [k v])))
           qmap)})

(defn expand-query-map
  ; leveraging the spec is much work but it means the spec and this code
  ; may more easily drift away.
  [env qmap]
  (let [{:keys [defaults qmap]} (unsugar-query-map env qmap)
        eid (:db/id qmap (gensym 'id))
        qmap (dissoc qmap :db/id)]
    {:eid eid
     :clauses (into []
                (concat
                  (mapcat (fn [[k v]]
                            ; PONDER: outputting recursive clauses after all non-rec
                            (if (map? v) ; recursive expansion
                              (let [{:keys [clauses], attr-eid :eid} (expand-query-map env v)]
                                (cons
                                  (if-some [k (reverse-lookup k)]
                                    [attr-eid k eid]
                                    (if-some [[_ default] (find defaults attr-eid)]
                                      [(list 'get-else '$ eid k default) attr-eid]
                                      [eid k attr-eid]))
                                  clauses))
                              (if-some [k (reverse-lookup k)]
                                [[v k eid]]
                                (when-not (find defaults v)
                                  [[eid k v]]))))
                    qmap)
                  (keep (fn [[k v]]
                          (when-some [[_ default] (find defaults v)]
                            [(list 'get-else '$ eid k default) v]))
                    qmap)))}))

#_(defn expand-strict-pull [[m v]]
   )

(defn expand-clause [env x]
  (cond
    (map? x) (:clauses (expand-query-map env x))
    #_#_(and (vector? x) (map? (first x)))
    (expand-strict-pull x)
    :else [x]))

(defn expand-query [env x]
  (let [x (if (map? x) [x] x)]
    (into [] (mapcat #(expand-clause env %)  x))))

;; keysets
(defn fresh-vars [expanded-q known-vars]
  (into {}
    (keep 
      (fn [x]
        (when (and (symbol? x) (not ('#{_ $} x))
                (or (:fresh (meta x)) (not (known-vars x))))
          [x (gensym x)])))
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
              [[]]))
      if (let [[_ test then else] clause]
           (recur (list 'or (list 'and test then) (list 'and (list 'not test) then))))
      (= not=) [[clause]])
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
                    (not not=) nil
                    = (let [syms (filter symbol? (next clause))]
                        (clj/for [a syms, b syms
                                  :when (not= a b)]
                          [a b])))
                  ; else must be a vector
                  (let [[e a v] (into clause '[_ _ _])]
                    (when-not (symbol? a)
                      (cond
                        (= '_ e) (when-not (= '_ v) [[v v]])
                        (= '_ v) [[e e]]
                        (symbol? e)
                        (cond
                          (symbol? v)
                          (if (= :db.cardinality/one (get-in schema [a :db/cardinality] :db.cardinality/one))
                            [[e v]]
                            [[v v]]) ; self reference or else it may become unreachable
                          (get-in schema [a :db/unique]) [[:known e]])
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

;; hiccup-style template
(defn- handler [expr]
  `(txing-handler (fn [~'% ~'%this]
                    ~expr)))

(defn used-vars
  "vars must be a predicate"
  [expr known-vars]
  ; TODO make it right: it's an overestimate
  (set (filter known-vars (cons expr (tree-seq coll? seq expr)))))

(defn lift-expressions
  "Returns [expressions hollowed-x] where
   expressions is a sequence of [path expression] and hollowed-x is x where symbols and
   sequences have been replaced by nil."
  [env known-vars x]
  (cond
    (associative? x)
    (reduce-kv (fn [[exprs x] k v]
                 (let [v (if (and (keyword? k) (.startsWith (name k) "on-"))
                           (handler v)
                           v)
                       [subexprs v] (lift-expressions env known-vars v)]
                   [(into exprs
                      (clj/for [[path subexpr] subexprs]
                        [(cons k path) subexpr]))
                    (assoc x k v)]))
      [{} x] x)
    (seq? x)
    (let [env' (update env :locals into (map (fn [sym] [sym {:name sym}])) (keys known-vars))
          x' (ana/macroexpand-1 env' x)]
      (if (= x x')
        [{nil x} nil]
        (recur env known-vars x')))
    (symbol? x) [{nil x} nil]
    :else [{} x]))

(defn terminal [env known-vars expr]
  (let [args (used-vars expr known-vars)]
    (reify Template
      (get-schema [_] nil)
      (emit-cljs [_ schema]
        `(terminal-template '[~@(map #(apply-aliases % known-vars) args)] (fn [[~@args]] ~expr))))))

(defn fragment* [env known-vars body options]
  (let [[exprs body] (lift-expressions env known-vars (vec body))
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
                                        (if (seq? e)
                                          [(apply-aliases e known-vars) arg]
                                          (list '= (known-vars e e) arg)))
                                      (next expr) args)]
                                (when-not (= (count args) (count (next expr)))
                                  (throw (ex-info (str "Arity mismatch: " (first expr) " got " (count (next expr)) " arguments.")
                                           {:expr expr
                                            :expected args})))
                                (reify Template
                                  (get-schema [_] (::schema meta))
                                  (emit-cljs [_ schema] `(include-template '~clauses ~name))))
                              :else
                              (terminal env known-vars expr)))])]
    (reify Template
      (get-schema [_] (transduce (map (comp get-schema second)) (partial merge-with into) (:schema options {}) children))
      (emit-cljs [_ schema]
        `(fragment-template ~body
           [~@(clj/for [[path child] children] [`'~path (emit-cljs child schema)])])))))

(defn state [env known-vars qmap body options]
  (let [{:keys [eid clauses]} (expand-query-map env qmap)
        known-vars (into known-vars
                     (assoc (fresh-vars clauses {}) ; empty known-vars because :state must not filter
                       eid (gensym eid)))
        clauses (map #(apply-aliases % known-vars) clauses)
        child (fragment* env known-vars body options)]
    (reify Template
      (get-schema [_] (get-schema child))
      (emit-cljs [_ schema]
        `(state-template '(ensure-state ~(gensym "sk") ~(known-vars eid) ~clauses) ~(emit-cljs child schema))))))

(defmacro ^:private if-valid
  ([bindings+spec+value then] `(if-valid ~bindings+spec+value ~then nil))
  ([[bindings spec value] then else]
    `(let [conformed# (s/conform ~spec ~value)]
       (if (= ::s/invalid conformed#)
         ~else
         (let [~bindings conformed#]
           ~then)))))

(s/def ::fragment-body
  (s/cat
    :options (s/* (s/cat :key keyword? :value any?))
    :body (s/* any?)))

(defn fragment [env known-vars & body]
  (if-valid [{:keys [body options]} ::fragment-body body]
    (let [{qmap :state :as options} (into {} (map (juxt :key :value)) options)]
      (if qmap
        (state env known-vars qmap body options)
        (fragment* env known-vars body options)))
    (throw (ex-info "Invalid body" {:body body}))))

(s/def ::for-body
  (s/cat
    :options (s/* (s/cat :key keyword? :value any?))
    :body (s/* any?)))

(defn for [env known-vars q & body]
  (if-valid [{:keys [body options]} ::fragment-body body]
    (let [sort-expr (some (fn [{:keys [key value]}]
                           (when (= key :sort) value)) options)
          body (concat
                 (mapcat (fn [{:keys [key value]}]
                           (when-not (= key :sort) [key value]))
                   options)
                 body)
          q (expand-query env q)
          vars (fresh-vars q known-vars)
          known-vars' (into known-vars vars)
          ?q (apply-aliases q known-vars')
          child (apply fragment env known-vars' body)]
      (reify Template
        (get-schema [_] (get-schema child))
        (emit-cljs [_ schema]
          (let [own-keys (keyvars q schema known-vars)
                sort-expr (or sort-expr (vec own-keys))
                sort-args (vec (used-vars sort-expr known-vars'))
                own-keys (map #(apply-aliases % known-vars') own-keys)
                aliased-sort-args (map #(apply-aliases % known-vars') sort-args)] ; known-vars and not known-vars' because we care about vars that were previously known
            `(for-template '~?q '~own-keys '~aliased-sort-args (fn [[~@sort-args]] ~sort-expr)
              ~(emit-cljs child schema))))))
    (throw (ex-info "Invalid body" {:body body}))))

(defmacro deftemplate [name args & body]
  (let [aliases (into {} (clj/for [arg args] [arg (gensym arg)]))
        template (apply fragment &env aliases body)
        schema (get-schema template)]
    `(def ~(vary-meta name assoc ::template (mapv aliases args) ::schema schema)
      ~(emit-cljs template schema))))

#_(defmacro defrule [rulename args & clauses]
   (if (seq? args)
     `(do
        ~@(map (fn [args+clauses] `(defrule ~rulename ~@args+clauses)) (cons args clauses)))
     ))

(defmacro io-trigger [q & body]
  (let [q (expand-query &env q)
        vars (vec (used-vars `(do ~@body) (fresh-vars q {})))]
    `(io-trigger* '~q '~vars
       (fn ~vars ~@body))))