(ns enlivez.q
  (:require-macros [enlivez.q :as macros])
  (:require [datascript.core :as d]))

(defn indexed-attr? [db attr]
  (let [schema (get (:rschema db) attr)]
    (or (:db/unique schema) (:db/index schema))))

(defn ref-attr? [db attr]
  (let [schema (get (:rschema db) attr)]
    (= :db.type/ref (:db/valueType schema))))

(defn maybe-lookup-ref?
  [r]
  (or (sequential? r) (keyword? r)))

(defn maybe-a-ref?
  [r]
  (if (number? r)
    (pos? r)
    (maybe-lookup-ref? r)))

(defn resolve-ref [db r]
  (cond
    (number? r) (when (pos? r) r)
    (keyword? r) (some-> (first (d/datoms db :avet :db/ident r)) .-e)
    (sequential? r) (let [[a v] r]
                      (some-> (first (d/datoms db :avet a v)) .-e))))

(defn profile-digit [bound-vars pat]
  (cond
    (not (symbol? pat)) 0 ; v numbered as in "vio_"
    (= '_ pat) 3
    (bound-vars pat) 1
    :else 2))

(declare clause-vars clause-xform+bv)

(def pattern-xform+bv
  (let [xforms (macros/pattern-xforms-array)]
    (fn [pattern indices bound-vars]
      (let [e (nth pattern 0 '_)
            a (nth pattern 1 '_)
            v (nth pattern 2 '_)
            ei (profile-digit bound-vars e)
            ai (profile-digit bound-vars a)
            vi (profile-digit bound-vars v)
            profile-index (-> ei (* 4) (+ ai) (* 4) (+ vi))
            xform (aget xforms profile-index)]
        [(xform (indices '$)
           (case ei
             0 e
             (1 2) (indices e)
             nil)
           (case ai
             0 a
             (1 2) (indices a)
             nil)
          (case vi
            0 v
            (1 2) (indices v)
            nil))
        (cond-> bound-vars
          (= ei 2) (conj e)
          (= ai 2) (conj a)
          (= vi 2) (conj v))]))))

(defn pattern-vars [[e a v] rf acc]
  (cond-> acc
    (and (symbol? e) (not= '_ e)) (rf e)
    (and (symbol? a) (not= '_ a)) (rf a)
    (and (symbol? v) (not= '_ v)) (rf v)))

(defn or-xform+bv [branches indices bound-vars]
  (let [[xforms bv] (reduce
                      (fn [[xforms bv] branch]
                        (let [[xform bv'] (clause-xform+bv branch indices bound-vars)]
                          [(conj xforms xform) (into bv bv')]))
                      [[] '#{$}] branches)]
    [(fn [rf]
       (let [rfs (into [] (map #(% rf)) xforms)]
         (fn [acc ctx]
           (reduce (fn [acc rf] (rf acc ctx)) acc rfs))))
     bv]))

(defn and-xform+bv [clauses indices bound-vars]
  (reduce
    (fn [[xform bv] clause]
      (let [[xform' bv] (clause-xform+bv clause indices bv)]
        [(fn [rf] (xform (xform' rf))) bv]))
    [identity bound-vars] clauses))

(defn body-vars [clauses rf acc]
  (reduce
    (fn [acc clause]
      (clause-vars clause rf acc))
    acc
    clauses))

(defn not-xform+bv [clauses indices bound-vars]
  (let [[xform] (and-xform+bv clauses indices bound-vars)
        ; exception as signal because I don't want to deal with reduced? or special value everywhere
        trap (xform (fn [_ _] (throw xform)))] ; xform as sentinel
    [(fn [rf]
       (fn [acc ctx]
         (if (try
               (trap true ctx)
               (catch :default e
                 (when-not (identical? xform e) (throw e))
                 false))
           (rf acc ctx)
           acc)))
     bound-vars]))

(declare ^:dynamic *OK*)

; (if test then else) is a more efficient (or (and test then) (and (not test) then))
(defn if-xform+bv [[test then else] indices bound-vars]
  (let [[test-xform test-then-bv] (clause-xform+bv test indices bound-vars)
        [then-xform test-then-bv] (clause-xform+bv then indices test-then-bv)
        [else-xform else-bv] (clause-xform+bv else indices bound-vars)] ; xform as sentinel
    [(fn [rf]
       (let [then-rf (as-> rf rf
                       (then-xform rf)
                       (fn [acc ctx]
                         (set! *OK* true)
                         (rf acc ctx))
                       (test-xform rf))
             else-rf (else-xform rf)]
         (fn [acc ctx]
           (binding [*OK* false]
             (cond-> (then-rf acc ctx)
               (not *OK*) (else-rf ctx)))))) ; if not ok then acc is untouched
     (into test-then-bv else-bv)]))

(defn eq-slot-xform [i v]
  (fn [rf]
    (fn [acc ctx]
      (if (= v (aget ctx i))
        (rf acc ctx)
        acc))))

(defn eq-slots-xform [i j]
  (fn [rf]
    (fn [acc ctx]
      (if (= (aget ctx i) (aget ctx j))
        (rf acc ctx)
        acc))))

(defn set-slot-xform [i v]
  (fn [rf]
    (fn [acc ctx]
      (aset ctx i v)
      (rf acc ctx))))

(defn copy-slot-xform [from to]
  (fn [rf]
    (fn [acc ctx]
      (aset ctx to (aget ctx from))
      (rf acc ctx))))

(defn =-xform+bv [args indices bound-vars]
  (let [[v :as values] (seq (remove symbol? args))
        [in & other-ins :as ins] (seq (keep #(some-> % bound-vars indices) args))
        out-vars (remove bound-vars args)
        outs (keep indices out-vars)]
    [(cond
       values
       (if (apply = values)
         (as-> identity xform
           (transduce (map #(eq-slot-xform % v)) comp xform ins)
           (transduce (map #(set-slot-xform % v)) comp xform outs))
         (fn [rf] (fn [acc _] acc)))
       ins
       (as-> identity xform
         (transduce (map #(eq-slots-xform in %)) comp xform other-ins)
         (transduce (map #(copy-slot-xform in %)) comp xform outs))
       outs
       (throw (ex-info "Clause are not automatically reordered yet, can't apply" {}))
       :else
       identity)
     (into bound-vars out-vars)]))

(defn spy-xform+bv [_ indices bound-vars]
  [(fn [rf]
     (fn [acc ctx]
       (prn (into {} (map (fn [[v i]] [v (aget ctx i)])) indices))
       (rf acc ctx)))
   bound-vars])

(def builtins
  (atom {'vector vector 'ground identity 'identity identity '= =
         'not= not=
         'get-else (fn [$ e a else]
                     (if-some [[datom] (when (maybe-a-ref? e)
                                         (seq (d/datoms $ :eavt e a)))]
                       (.-v datom)
                       else))}))

(defn register-fn [sym f]
  (swap! builtins assoc sym f))

#_#_(defn ground-xforms+bv [f [arg] ret indices bound-vars]
    (let [iret (indices ret)]
      [(fn [rf]
         (fn [acc ctx]
           (aset ctx iret arg)
           (rf acc ctx)))
       (conj bound-vars ret)]))

(defn get-else-xforms+bv [f [$ ] ret indices bound-vars]
  (let [iret (indices ret)]
    [(fn [rf]
       (fn [acc ctx]
         (aset ctx iret arg)
         (rf acc ctx)))
     (conj bound-vars ret)]))

(defn fn-call-xforms+bv [f args ret indices bound-vars]
  (let [args (to-array args)
        setters (into [] (keep-indexed (fn [i arg]
                                         (when-some [j (indices arg)]
                                           (when-not (bound-vars arg)
                                             (throw (ex-info (str "Can't call function " f " with unbound argument " arg)
                                                      {:arg arg
                                                       :clause (cons f args)})))
                                           #(do (aset args i (aget % j)) %)))) args)
        f (case (count args)
            0 f
            1 (fn [] (f (aget args 0)))
            2 (fn [] (f (aget args 0) (aget args 1)))
            3 (fn [] (f (aget args 0) (aget args 1) (aget args 2)))
            4 (fn [] (f (aget args 0) (aget args 1) (aget args 2) (aget args 3)))
            (fn [] (apply f (aclone args))))
        iret (indices ret)]
    (if ret
      [(fn [rf]
         (fn [acc ctx]
           (reduce (fn [ctx setter] (setter ctx)) ctx setters)
           (if-some [ret (f)]
             (rf acc (doto ctx (aset iret ret)))
             acc)))
       (conj bound-vars ret)]
      ; predicate call
      [(fn [rf]
         (fn [acc ctx]
           (reduce (fn [ctx setter] (setter ctx)) ctx setters)
           (if (f) (rf acc ctx) acc)))
       bound-vars])))

(defn clause-xform+bv [clause indices bound-vars]
  (cond
    (vector? clause)
    (if (seq? (nth clause 0))
      ; binding
      (let [[expr out] clause]
        (if-some [f (@builtins (first expr))]
          (fn-call-xforms+bv f (next expr) out indices bound-vars)
          (throw (ex-info "Unexpected expr" {:expr expr}))))
      (pattern-xform+bv clause indices bound-vars))
    ; pattern or binding
    (seq? clause)
    (case (first clause)
      spy (spy-xform+bv clause indices bound-vars)
      or (or-xform+bv (next clause) indices bound-vars)
      and (and-xform+bv (next clause) indices bound-vars)
      not (not-xform+bv (next clause) indices bound-vars)
      if (if-xform+bv (next clause) indices bound-vars)
      or-else (let [[_ test else] clause]
                (if-xform+bv [test '(and) else] indices bound-vars))
      = (=-xform+bv (next clause) indices bound-vars)
      not= (clause-xform+bv (list 'not (cons '= (next clause))) indices bound-vars)
      (throw (ex-info "Unexpected clause shape" {:clause clause})))
    :else
    (throw (ex-info "Unexpected clause shape" {:clause clause}))))

(defn clause-vars [clause rf acc]
  (cond
    (vector? clause)
    (if (seq? (nth clause 0))
      (let [[expr out] clause]
        (if (some? out) (rf acc out) acc))
      (pattern-vars clause rf acc))
    ; pattern or binding
    (seq? clause)
    (case (first clause)
      spy acc
      (or and not if or-else) (body-vars (next clause) rf acc)
      = (reduce ((filter symbol?) rf) acc (next clause))
      not= (clause-vars (list 'not (cons '= (next clause))) rf acc)
      (throw (ex-info "Unexpected clause shape" {:clause clause})))
    :else
    (throw (ex-info "Unexpected clause shape" {:clause clause}))))

(defn allocate-indices [init clause]
  (let [rf (fn [m v]
             (if (m v) m (assoc! m v (count m))))]
    (persistent! (clause-vars clause rf (transient init)))))

(defn prepare-query [find where-clauses]
  (let [clause (cons 'and where-clauses)
        indices (allocate-indices '{$ 0} clause)
        find-indices (into [] (map indices) find)
        n (count indices)
        rf (fn [s ctx]
             (conj! s (into [] (map #(aget ctx %)) find-indices)))
        [xform bv] (clause-xform+bv clause indices '#{$})
        rf (xform rf)] ; ok to reuse, rf and xform are stateless
    (fn [db]
      (let [ctx (doto (object-array n) (aset 0 db))]
        (persistent! (rf (transient #{}) ctx))))))
