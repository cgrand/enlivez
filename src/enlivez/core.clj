(ns enlivez.core
  (:refer-clojure :exclude [for])
  (:require [clojure.core :as clj]
    [clojure.string :as str]
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

(defn- interop? [sym]
  (and (simple-symbol? sym) (.startsWith (name sym) ".")))

(defn resolve-var
  "returns a var map"
  [env sym throw-or-nil]
  (let [known (volatile! true)
        v (ana/resolve-var (:host-env env) sym
            (fn [env prefix suffix]
              (ana/confirm-var-exists env prefix suffix
                (case throw-or-nil
                  :throw (ana/confirm-var-exists-throw)
                  :nil (fn [env prefix suffix]
                         (vreset! known false))))))]
    (when @known v)))

(defn- resolver [&env]
  (if (:ns &env)
    (fn [sym]
      (if (or (and (seq? sym) (= 'var (first sym))) (impl/special? sym) (impl/special-pred? sym)
            (interop? sym))
        sym
        (let [env {:host-env &env :known-vars #{}}
              {:keys [name meta]} (resolve-var env sym :throw)]
          (if (::rule meta)
            name
            (list 'var name)))))
    (fn [sym]
      (if (or (and (seq? sym) (= 'var (first sym))) (impl/special? sym) (impl/special-pred? sym)
            (interop? sym))
        sym
        (if-some [v (ns-resolve *ns* &env sym)]
          (let [m (meta v)
                name (symbol (-> m :ns ns-name name) (-> m :name name))]
            (if (::rule m)
              name
              (list 'var name)))
         (throw (ex-info (str "Unable to resolve symbol: " sym) {:sym sym :ns *ns*})))))))

(s/def ::defrule
  (s/cat :name simple-symbol? :doc (s/? string?)
    :args vector? :kind #{:- :=} :clauses (s/* any?)))

(s/def ::defcase
  (s/cat :name symbol? :hint (s/? keyword?)
    :args vector? :kind #{:- :=} :clauses (s/* any?)))

(defmacro defrule
  "Defines an EZ rule with an optional implementation."
  {:arglists '([name doc? [args*]]
                [name doc? [args*] clause+])}
  [& body]
  (when-valid [{:keys [doc args kind clauses] the-name :name} ::defrule body]
    (let [pure-args (cond-> (into [] (map #(if (symbol? %) % (gensym "_"))) args)
                      (and (= := kind) (not-any? #{'%} args)) (conj '%))
          decl `(def ~(cond-> (vary-meta the-name assoc :arglists `'~(list pure-args) ::rule true)
                        doc (vary-meta assoc :doc doc)) {})]
      (if clauses
        `(do ~decl (defcase ~the-name ::defrule ~args ~kind ~@clauses))
        decl))))

(defn- quote-clause [[pred & args :as clause]]
  (cond
    (= 'not pred) `(list '~'not ~(quote-clause (first args)))
    (= '. pred)
    (let [[obj meth & meth-args] args
          fn-args (filter simple-symbol? (cons obj (butlast meth-args)))]
      `(list '~'call (fn [~@(butlast fn-args)] (~pred ~@(butlast args)))
         ~@(map #(list 'quote %) fn-args)))
    (interop? pred)
    (let [fn-args (filter simple-symbol? args)]
      `(list '~'call (fn [~@(butlast fn-args)] (~pred ~@(butlast args)))
         ~@(map #(list 'quote %) fn-args)))
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

(defn analyze-expr
  "Analyze an expression."
  [&env expr ret-var]
  (analyze-q &env [(list 'eq expr ret-var)]))

(defmacro defcase
  {:arglists '([name hint? [args*] clause+])}
  [& body]
  (when-valid [{:keys [hint args kind clauses] the-name :name} ::defcase body]
    (let [hint (or hint (keyword (gensym "case")))
          full-name (symbol (-> *ns* ns-name name) (name the-name))
          veqs (volatile! [])
          args (into []
                 (map #(if (symbol? %)
                         %
                         (let [arg (gensym "arg")]
                           (vswap! veqs conj (list 'eq % arg))
                           arg)))
                 args)
          args (cond-> args
                 (and (= := kind) (not-any? #{'%} args))
                 (conj '%))
          clauses (case kind
                    :- (vec clauses)
                    := [(list 'eq '% (cons 'and clauses))])
          clauses (into clauses @veqs)
          {:keys [deps expansion]} (analyze-case &env full-name args clauses)
          expr `{::case '~(cons (cons full-name args) clauses)
                 ::expansion ~expansion
                 ::deps [~@(map (fn [x] `(var ~x)) deps)]}]
      `(do
         ~(if (:ns &env)
            `(set! ~the-name (assoc ~the-name ~hint ~expr))
            `(alter-var-root (var ~the-name) assoc ~hint ~expr))
         (var ~the-name)))))

(defn expand-relational-expression
  "Returns (eq query var)"
  [expr]
  (let [exprs (impl/unnest (list 'dummy expr))
        [_dummy var] (peek exprs)
        exprs (pop exprs)]
    (list 'eq (if (next exprs)
                (list 'and exprs)
                (first exprs)) var)))

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
(defn used-vars
  "vars must be a predicate"
  [expr known-vars]
  ; TODO make it right: it's an overestimate
  (set (filter known-vars (cons expr (tree-seq coll? seq expr)))))

(declare handler-call)

(defn lift-expressions
  "Returns [expressions hollowed-x] where
   expressions is a sequence of [path expression] and hollowed-x is x where symbols and
   sequences have been replaced by nil."
  [x mode]
  (cond
    (associative? x)
    (reduce-kv (fn [[exprs x] k v]
                 (let [v (if (and (= :html mode) (keyword? k) (.startsWith (name k) "on-"))
                           (list `handler-call v)
                           v)
                       [subexprs v] (lift-expressions v mode)]
                   [(into exprs
                      (clj/for [[path subexpr] subexprs]
                        [(cons k path) subexpr]))
                    (assoc x k v)]))
      [{} x] x)
    (seq? x) [{nil x} nil]
    (symbol? x) [{nil x} nil]
    :else [{} x]))

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

(defn handler-terminal [env rel-expr]
  (let [&env (:host-env env)
        [_eq q ret] (expand-relational-expression rel-expr)
        rethead (list (gensym "tx") ret)
        {rule-vars :vars
         rule-bodies :bodies
         support-rules :support-rules
         deps :deps} (analyze-q &env [q])
        args (filter (:known-vars env) rule-vars)
        handler-activation (list* (gensym "handler-activation") '%event '%this args)
        rules `(concat
                 (clj/for [body# ~rule-bodies]
                   (list* '~rethead '~handler-activation body#))
                 ~support-rules)
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
        `(let [handler# (handler '~(first handler-activation) '~(first rethead)
                          ~rules [~@(map (fn [x] `(var ~x)) deps)])]
           (terminal-template [~rule]
             (fn [args#]
               (handler# args#))))))))

(defn terminal-expr [{&env :host-env :keys [activation known-vars]} expr]
  (if (symbol? expr)
    (let [v expr
          expr-activation (list (gensym "expr-activation") (gensym "path"))
          rules [(quote-rule
                   (list expr-activation activation
                     (list '(var conj) (second activation) v (second expr-activation))))
                 (quote-rule (list (list `component-path (second expr-activation)) expr-activation))]]
      (reify Template
        (emit-cljs [_]
          `(expr-template [~@rules] [] '~v))))
    (let [v (gensym "term-expr")
          {rule-vars :vars
           rule-bodies :bodies
           support-rules :support-rules
           deps :deps} (analyze-expr &env expr v)
          expr-activation (list (gensym "expr-activation") (gensym "path"))
          qhead (cons (gensym "q") rule-vars)
          rules (list*
                  (quote-rule
                    (list expr-activation activation qhead
                      (list '(var conj) (second activation) v (second expr-activation))))
                  (quote-rule (list (list `component-path (second expr-activation)) expr-activation))
                  (map (fn [body-expr] `(cons '~qhead ~body-expr)) rule-bodies))]
      (reify Template
        (emit-cljs [_]
          `(expr-template
             [~@rules] [~@(map (fn [x] `(var ~x)) deps)]
             '~v))))))

(defn fragment* [env body options]
  (let [[exprs body] (lift-expressions (vec body) :html)
        &env (:host-env env)
        children (clj/for [[path expr n] (map-indexed #(conj %2 %1) exprs)
                           :let [[hints] (reduce (fn [[hints e] i]
                                                   [(if (and (vector? e) (keyword? (first e)))
                                                      (conj hints (name (first e)) i)
                                                      (conj hints (cond-> i (keyword? i) name))) (get e i)])
                                           [[] body] path)
                                 hint (str/join "-" hints)
                                 pathvar (gensym "path")
                                 [_ ppathvar & args :as activation] (:activation env)
                                 child-activation
                                 `((~(gensym (str "child-" hint "_")) ~pathvar ~@args)
                                    ~activation
                                    ((var conj) ~ppathvar ~n ~pathvar))
                                 env (assoc env :activation (first child-activation))]]
                   [path (let [{:keys [meta name]}
                               (when-some [x (when (seq? expr) (first expr))]
                                 (when (symbol? x) (resolve-var env x :nil)))]
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
                               enlivez.core/handler-call (handler-terminal env (second expr))
                               (terminal-expr env expr))
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
  (let [#_#_[exprs state-map] (lift-expressions state-map :entity-map)
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
            ~(emit-cljs child))))))

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

(defn for [{&env :host-env :keys [activation known-vars]} pseudo-bindings & body]
  (when-valid [{:keys [body options]} ::fragment-body body]
    (let [q (map
              (fn [[lh rh]]
                (case lh
                  :when rh
                  (list 'eq lh rh)))
              (partition 2 pseudo-bindings))
          sort-expr (or (some (fn [{:keys [key value]}]
                              (when (= key :sort) value)) options) :no-sort)
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
          child-activation (list* (gensym "for-dom-activation")
                             (gensym "path") known-vars')
          child (apply fragment {:host-env &env
                                 :known-vars known-vars'
                                 :activation child-activation} body)
          sort-activation (list* (gensym "for-sort-activation")
                            (gensym "path") known-vars')
          sort-child (terminal-expr {:host-env &env
                                     :known-vars known-vars'
                                     :activation sort-activation}
                       sort-expr)]
      (reify Template
        #_(get-schema [_] (get-schema child))
        (emit-cljs [_]
          `(for-template '~activation
             '~child-activation ~(emit-cljs child)
             '~sort-activation ~(emit-cljs sort-child)
             '~rule-vars ~rule-bodies
             {:rules ~support-rules :deps [~@(map (fn [x] `(var ~x)) deps)]}))))))

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

(defmacro deftrigger
  "Register side-effecting code (IO) to run for each query match."
  [trigger-name q & body]
  (let [{:keys [start stop]} (case (first body)
                               (:start :stop) (apply hash-map body)
                               {:start (cons 'do body)})
        qname (symbol (-> *ns* ns-name name) (name trigger-name))
        {:keys [vars bodies support-rules deps]} (analyze-q &env q)
        qhead (cons qname vars)
        rules (concat
                [(quote-rule
                  `[(component-path path#) ~qhead
                    ((var vector)
                      (fn [~@(next qhead)] ~start)
                      (fn [~@(next qhead)] ~stop)
                      ~@(next qhead) comp#)
                    ((var vector) :trigger comp# path#)])]
                (clj/for [body bodies]
                  `(cons '~qhead ~body))
                support-rules)]
    `(io-trigger* ~(keyword qname) [~@rules] [~@(map (fn [x] `(var ~x)) deps)])))

