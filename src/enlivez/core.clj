(ns enlivez.core
  (:refer-clojure :exclude [for])
  (:require [clojure.core :as clj]
    [cljs.analyzer :as ana]
    [clojure.spec.alpha :as s]
    [enlivez.q :as q]
    [enlivez.impl.seminaive :as impl]))

(declare for)

(defmacro ^:private DEPRECATED []
  `(throw (ex-info "DEPRECATED" {})))

(defmacro ^:private TODO []
  `(throw (ex-info "TODO" {})))

(defmacro ^:private when-valid
  [[bindings spec value] & body]
    `(let [value# ~value
           spec# ~spec
           conformed# (s/conform spec# value#)]
       (if (= ::s/invalid conformed#)
         (throw (ex-info "Invalid input" {:value value# :spec spec#}))
         (let [~bindings conformed#]
           ~@body))))

;; rules

(defn- resolver [env]
  (if (:ns env)
    (fn [sym]
      (if (or (impl/special? sym) (impl/special-pred? sym))
        sym
        (let [{:keys [name meta]} (ana/resolve-var env sym (ana/confirm-var-exists-throw))]
          (if (::rule meta)
            name
            (list 'var name)))))
    (fn [sym]
      (if (or (impl/special? sym) (impl/special-pred? sym))
        sym
        (if-some [v (ns-resolve *ns* env sym)]
          (let [m (meta v)
                name (symbol (-> m :ns ns-name name) (-> m :name name))]
            (if (::rule m)
              name
              (list 'var name)))
         (throw (ex-info (str "Unable to resolve symbol: " sym) {:sym sym :ns *ns*})))))))

(s/def ::args (s/coll-of simple-symbol? :kind vector?))

(s/def ::defrule
  (s/cat :name simple-symbol? :doc (s/? string?)
    :args ::args :clauses (s/? (s/+ any?))))

(s/def ::defcase
  (s/cat :name symbol? :hint (s/? keyword?)
    :args ::args :clauses (s/+ any?)))

(defmacro defrule
  "Defines an EZ rule with an optional implementation."
  {:arglists '([name doc? [args*]]
                [name doc? [args*] clause+])}
  [& body]
  (when-valid [{:keys [doc args clauses] the-name :name} ::defrule body]
    (let [decl `(def ~(cond-> (vary-meta the-name assoc :arglists `'~(list args) ::rule true)
                        doc (vary-meta assoc :doc doc)) {})]
      (if clauses
        `(do ~decl (defcase ~the-name ::defrule ~args ~@clauses))
        decl))))

(defn- quote-clause [[pred & args :as clause]]
  (cond
    (= 'not pred) `(list '~'not ~(quote-clause (first args)))
    (symbol? pred) `(list '~pred ~@(map (fn [x] (if (symbol? x) (list 'quote x) x)) args))
    (= 'var (first pred)) `(list '~'call ~pred
                             ~@(map (fn [x] (if (symbol? x) (list 'quote x) x)) args))
    :else (throw (ex-info (str "Unable to quote " clause) {:clause clause}))))

(defn- quote-clauses [clauses]
  `(list ~@(map quote-clause clauses)))

(defn- quote-rule [[head & clauses :as rule]]
  `(list '~head ~@(map quote-clause clauses)))

(defn analyze-case
  "Returns a map with two keys:
   :deps, a collection of qualified symbols of rules the input case depends upon,
   :expansion, a clojure expression that evaluates to a datalog expression."
  ([&env full-name args clauses]
    (analyze-case &env full-name args clauses #{}))
  ([&env full-name args clauses whitelist]
    (let [rule (cons (cons full-name args) clauses)
          resolve (resolver &env)
          vdeps (volatile! #{})
          resolve (fn [x]
                    (if (whitelist x)
                      x
                      (let [x (resolve x)]
                        (when (and (qualified-symbol? x) (not (impl/special-pred? x)))
                          (vswap! vdeps conj x))
                        x)))
          all-rules (into [] (map quote-rule) (impl/lift-all [rule] resolve))] ; side effects don't reorder across this binding
      {:expansion all-rules
       :deps @vdeps})))

(defn analyze-q
  "Analyze a query."
  [&env clauses]
  ; add line info ?
  (let [tmp-name (gensym 'q)
        rule (cons (list tmp-name) clauses)
        resolve (resolver &env)
        vdeps (volatile! #{})
        resolve (fn [x]
                  (let [x (resolve x)]
                    (when (and (qualified-symbol? x) (not (impl/special-pred? x)))
                      (vswap! vdeps conj x))
                    x))
        all-rules (impl/lift-all [rule] resolve)
        all-rules (vec all-rules) ; side effects! don't reorder across this binding
        args ; args is the intersection of vars of each rule
        (transduce
          (keep (fn [[[pred] & clauses]]
                  (when (= pred tmp-name)
                    (into #{} (mapcat impl/used-vars) clauses))))
          (fn
            ([a] a)
            ([a b] (transduce (remove a) disj b b)))
          identity all-rules)
        support-rules (into []
                        (comp
                          (remove (fn [[[h]]] (= h tmp-name)))
                          (map quote-rule))
                        all-rules)
        bodies (into [] 
                 (comp
                   (keep (fn [[[h] & clauses :as rule]]
                           (when (= h tmp-name) clauses)))
                   (map quote-clauses))
                 all-rules)] 
    {:vars args
     :bodies bodies
     :support-rules support-rules
     :deps @vdeps}))

(defmacro defcase
  {:arglists '([name hint? [args*] clause+])}
  [& body]
  (when-valid [{:keys [hint args clauses] the-name :name} ::defcase body]
    (let [hint (or hint (keyword (gensym "case")))
          full-name (symbol (-> *ns* ns-name name) (name the-name))
          {:keys [deps expansion]} (analyze-case &env full-name args clauses)
          expr `{::case '~(cons (cons full-name args) clauses)
                 ::expansion ~expansion
                 ::deps [~@(map (fn [x] `(var ~x)) deps)]}]
      `(do
         ~(if (:ns &env)
            `(set! ~the-name (assoc ~the-name ~hint ~expr))
            `(alter-var-root (var ~the-name) assoc ~hint ~expr))
         (var ~the-name)))))

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
;; end of rules

(defprotocol Template
  #_(get-schema [_])
  (emit-cljs [_]))

;; query maps syntax
(defn- reverse-lookup
  "Returns the direct keyword when the input keyword is reversed, else returns nil."
  [k]
  (when-some [[_ n] (when (keyword? k) (re-matches #"_(.*)" (name k)))]
    (keyword (namespace k) n)))

(defn keywordize [sym env]
  (let [ns (some->>
             (when-some [ns (namespace sym)]
               (or (ana/resolve-ns-alias env ns nil) (ana/resolve-macro-ns-alias env ns)))
             name)]
    (keyword (or ns (name (ns-name *ns*))) (name sym))))

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
                 [(keywordize k env) (symbol (name k))] ; auto keyword
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
    (seq? x) (case (first x)
               and (mapcat #(expand-clause env %) (rest x))
               not [(cons 'not (mapcat #(expand-clause env %) (rest x)))]
               or [(cons 'or (map #(cons 'and (expand-clause env %)) (rest x)))]
               (= not= if or-else) [x])
    #_#_(and (vector? x) (map? (first x)))
    (expand-strict-pull x)
    :else [x]))

(defn expand-query [env x]
  (let [x (cond
            (map? x) [x]
            (seq? x) [x]
            (vector? x) x
            :else (throw (ex-info "Unexpecetd query shape, it can be a map, a list or a vector." {:q x})))]
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


;; hiccup-style template
(defn- handler [expr]
  `(txing-handler (fn [~'% ~'%this ~'%db] ~expr)))

(defn used-vars
  "vars must be a predicate"
  [expr known-vars]
  ; TODO make it right: it's an overestimate
  (set (filter known-vars (cons expr (tree-seq coll? seq expr)))))

(defn expand-relational-expression
  "Returns [query var]"
  [expr]
  (let [exprs (impl/unnest (list 'dummy expr))
        [_dummy var] (peek exprs)
        exprs (pop exprs)]
    [exprs var]))

(defn lift-expressions
  "Returns [expressions hollowed-x] where
   expressions is a sequence of [path expression] and hollowed-x is x where symbols and
   sequences have been replaced by nil."
  [env x mode]
  (let [known-vars (:known-vars env)]
    (cond
      (associative? x)
      (reduce-kv (fn [[exprs x] k v]
                   (let [v (if (and (= :html mode) (keyword? k) (.startsWith (name k) "on-"))
                             (handler v)
                             v)
                         [subexprs v] (lift-expressions env v mode)]
                     [(into exprs
                        (clj/for [[path subexpr] subexprs]
                          [(cons k path) subexpr]))
                      (assoc x k v)]))
        [{} x] x)
      (seq? x)
      (let [host-env' (update (:host-env env) :locals into (map (fn [sym] [sym {:name sym}])) known-vars)
            x' (ana/macroexpand-1 host-env' x)]
        (if (= x x')
          [{nil x} nil]
          (recur env x' mode)))
     (symbol? x) [{nil x} nil]
     :else [{} x])))

(defn terminal [env expr]
  (let [args (used-vars expr (:known-vars env)) ; call vec to fix ordering
        activation (:activation env)
        activation-path (second activation)
        rule (quote-rule
               `((component-path path#) ;-
                  ~activation
                  ((var vector) ~@args v#)
                  ((var conj) ~activation-path v# path#)))]
    (reify Template
      #_(get-schema [_] nil)
      (emit-cljs [_]
        `(terminal-template [~rule] (fn [[~@args]] ~expr))))))

(defn fragment* [env body options]
  (let [[exprs body] (lift-expressions env (vec body) :html)
        &env (:host-env env)
        children (clj/for [[paths expr n] (map-indexed #(conj %2 %1) exprs)
                           :let [pathvar (gensym "path")
                                 [_ ppathvar & args :as activation] (:activation env)
                                 child-activation
                                 `((~(gensym (str "child-" n "_")) ~pathvar ~@args)
                                    ~activation
                                    ((var conj) ~ppathvar ~n ~pathvar))
                                 env (assoc env :activation (first child-activation))]]
                   [paths (let [{:keys [meta name]}
                                (when-some [x (and (seq? expr) (first expr))]
                                  (when (symbol? x) (some->> x (ana/resolve-var &env))))]
                            (cond
                              (::special meta)
                              (apply @(resolve name) env (next expr)) ; TODO inclusion
                              (::activation meta)
                              (let [call-site-activation (:activation env)
                                    callee-activation (::activation meta)
                                    unnested-call (or (impl/unnest expr) [expr])
                                    clauses (pop unnested-call)
                                    args (next (peek unnested-call))
                                    vclauses (volatile! clauses)
                                    args
                                    (into []
                                      (map
                                        (fn [arg callee-arg]
                                          (if (symbol? arg)
                                            arg
                                            (let [arg' (gensym callee-arg)]
                                              (vswap! vclauses conj (list 'eq arg' arg))
                                              arg')))
                                        args (nnext callee-activation)))
                                    clauses @vclauses
                                    {:keys [deps expansion]}
                                    (analyze-case &env
                                      (first callee-activation)
                                      (cons (second call-site-activation) args)
                                      (cons call-site-activation
                                        clauses)
                                      #{(first call-site-activation)})
                                    deps (conj deps (list 'var name))]
                                ; This is interesting but not fully handled: using nested stuff we can trigger implicit iteration
                                ; should expressions be allowed as args?
                                ; only when returning 1 result? or 0?
                                (reify Template
                                  #_(get-schema [_] (::schema meta))
                                  (emit-cljs [_] `(include-template (var ~name) [~@deps] ~expansion))))
                              (seq? expr)
                              (case (first expr)
                                clojure.core/unquote (terminal env (second expr)) ; cljs escape hatch
                                (let [[q var] (expand-relational-expression expr)]
                                  (for env q var)))
                              (symbol? expr)
                              (terminal env expr)
                              :else (throw (ex-info (str "Unexpected expression: " (pr-str expr)) {:expr expr}))))
                    child-activation])]
    (reify Template
      #_(get-schema [_] (transduce (map (comp get-schema second)) (partial merge-with into) (:schema options {}) children))
      (emit-cljs [_]
        `(fragment-template ~body
           [~@(clj/for [[path child activation] children]
                [`'~path (emit-cljs child) (quote-rule activation)])])))))


(defn state [env state-map body options]
  (let [#_#_[exprs state-map] (lift-expressions env state-map :entity-map)
        state-var (or (:db/id state-map) (gensym "state"))
        state-map (dissoc state-map :db/id)
        known-vars' (conj (:known-vars env) state-var)
        [_ activation-path :as activation] (map #(if (= % state-var) (gensym "_") %) (:activation env)) ; state-var shadowing
        init-rule `[(component-path path#)  ~activation ((var conj) ~activation-path ~activation-path path#)]
        state-activation (list* (gensym "state-activation")
                           (gensym "path")
                           activation-path ; state key
                           (disj (:known-vars env) state-var))
        child-activation (list* (gensym "state-body-activation")
                           (second state-activation)
                           known-vars')
        rules
        `[[~state-activation ~activation ((var conj) ~activation-path ~activation-path ~(second state-activation))]
          [(component-path ~(second state-activation)) ~state-activation]
          [~child-activation ~state-activation
           (impl/datom ~state-var ::key ~activation-path)]]
        child (fragment* 
                (assoc env :known-vars known-vars' :activation child-activation)
                body options)]
    (reify Template
       #_(get-schema [_] (get-schema child))
       (emit-cljs [_]
         ; TODO state-map may be expression (at least values)
         `(state-template ~state-map
            [~@(map quote-rule rules)]
            ~(emit-cljs child))))
    )
  #_(let [state-entity (state-entity-map env state-map)
         state-query (state-query-map env state-map)
         state-query (when (seq state-query) state-query)
         eid (:db/id state-entity '_)
         eid (if (and state-query (= '_ eid))
               'state-eid
               eid)
         known-vars (case eid
                      _ known-vars
                      (assoc known-vars eid (gensym eid)))
         state-query (some-> state-query (assoc :db/id eid))
         state-entity (dissoc state-entity :db/id)
         args (vec (used-vars state-entity known-vars))
         child (if state-query
                 (apply for env known-vars state-query body)
                 (fragment* env known-vars body options))]
     (reify Template
       #_(get-schema [_] (get-schema child))
       (emit-cljs [_]
         ; TODO state-map may be expression (at least values)
         `(state-template '~(known-vars eid '_) '~(mapv known-vars args) (fn [~args] ~state-entity) ~(emit-cljs child))))))

(s/def ::fragment-body
  (s/cat
    :options (s/* (s/cat :key keyword? :value any?))
    :body (s/* any?)))

(defn fragment [env & body]
  (when-valid [{:keys [body options]} ::fragment-body body]
    (let [{state-map :state :as options} (into {} (map (juxt :key :value)) options)]
      (if state-map
        (state env state-map body (dissoc options :state))
        (fragment* env body options)))))

(s/def ::for-body
  (s/cat
    :options (s/* (s/cat :key keyword? :value any?))
    :body (s/* any?)))

(defn for [{&env :host-env :keys [activation known-vars]} q & body]
  (when-valid [{:keys [body options]} ::fragment-body body]
    (let [sort-expr (some (fn [{:keys [key value]}]
                           (when (= key :sort) value)) options)
          body (concat
                 (mapcat (fn [{:keys [key value]}]
                           (when-not (= key :sort) [key value]))
                   options)
                 body)
          {rule-vars :vars
           rule-bodies :bodies
           support-rules :support-rules
           deps :deps} (analyze-q &env q)
          known-vars' (into known-vars rule-vars)
          child-activation (list* (gensym "for-body-activation")
                             (gensym "path") known-vars')
          child (apply fragment {:host-env &env
                                 :known-vars known-vars'
                                 :activation child-activation} body)]
      (reify Template
        #_(get-schema [_] (get-schema child))
        (emit-cljs [_]
          (let [sort-args (when sort-expr (vec (used-vars sort-expr known-vars')))
                sort-fn (when sort-expr
                          `(fn [[~@sort-args]] ~sort-expr))]
            `(for-template '~activation '~child-activation
               '~rule-vars ~rule-bodies
               {:rules ~support-rules :deps [~@(map (fn [x] `(var ~x)) deps)]}
               '~sort-args ~sort-fn
               ~(emit-cljs child))))))))

(defmacro template [activation args & body]
  (let [env {:host-env &env
             :activation activation
             :known-vars (set args)}]
    (emit-cljs (apply fragment env body))))

(defmacro deftemplate [template-name args & body]
  (let [qname (symbol (-> *ns* ns-name name) (name template-name))
        activation (list* qname (gensym "path") args)]
   `(do ; better trick to make self resolution works? 
      (def ~(vary-meta template-name assoc ::activation activation))
      (set! ~template-name (template ~activation ~args ~@body)))))

(defmacro defhandler
  "Defines a function suitable to be called in a handler expression.
   This functions takes a query after the arguments vector (no var-args, no destructuring atm).
   The body of the function will be evaluated for each match of the query.
   Arguments are bound in the query.
   All query vars are bound in the body."
  [name args q & body]
  ; TODO: support for desctructuring
  (let [where (expand-query &env q)
        vars (vec (used-vars `(do ~@body) (fresh-vars q {})))]
    `(def ~(vary-meta name assoc ::handler true)
       (let [q# '~where
             vars# '~vars
             pq# (q/prepare-query vars# q# '~args)]
         (fn ~args
           (mapcat
             (fn [~vars]
               (let [x# (do ~@body)]
                 (if (or (nil? x#) (sequential? x#)) x# [x#])))
             (pq# @@#'conn ~@args)))))))

(defmacro io-trigger [q & body]
  (let [q (expand-query &env q)
        vars (vec (used-vars `(do ~@body) (fresh-vars q {})))]
    `(io-trigger* '~q '~vars
       (fn ~vars ~@body))))

