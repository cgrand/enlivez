(ns enlivez.impl.seminaive
  (:require [datascript.core :as d]
    [cljs.analyzer :as ana]))

(defn- TODO [s]
  (throw (ex-info (str "TODO: " s) {})))

(def special? '#{or and not fresh let #_new #_if #_when})

(def ^:private ^:dynamic *env*)

(defn resolve-pred [sym]
  (cond
    (vector? sym) sym ; for internal derived preds
    (special? sym) sym
    (:ns *env*) ; cljs
    (:name (ana/resolve-var *env* sym (ana/confirm-var-exists-throw)))
    :else
    (if-some [m (-> sym resolve meta)]
      (symbol (name (ns-name (:ns m))) (name (:name m)))
      (throw (ex-info (str "Can't resolve \"" sym "\"") {:sym sym :env *env* :ns *ns*})))))

(defn used-vars
  [[op & args]]
  (if (special? op)
    (case op
      fresh (let [[new-vars & args] args]
              (remove (set new-vars) (mapcat used-vars args)))
      (not and or) (mapcat used-vars args))
    (filter #(and (symbol? %) (not= '_ %)) args)))

;; ok the goal here is to implement seminaive evaluation for a datalog program

(defn flatten-map
  "Returns a seq of clauses."
  ([clause]
    (let [id (or (:as clause) (gensym 'id))]
      (flatten-map clause id)))
  ([clause id]
    (cons 'and
      (for [[k v] (dissoc clause :as)]
        (list k id v)))))

(defn expand-kw-clause [[k & args] missing]
  (if (.startsWith (name k) "_")
    (let [k (keyword (namespace k) (subs (name k) 1))]
      (list `datom (nth args 1 missing) k (nth args 0)))
    (list `datom (nth args 0) k (nth args 1 missing))))

(defn- unnest
  "If clause has nested expressions then unnest them (not recursively) else nil."
  [[pred & args]]
  (let [vclauses (volatile! [])
        clause (into [pred]
                 (map (fn [arg]
                        (cond
                          (seq? arg)
                          (let [ret (gensym "ret")
                                arg (cond-> arg (keyword? (first arg)) (expand-kw-clause '%))
                                arg' (into [] (map (fn [x] ({'% ret} x x))) arg)]
                            (vswap! vclauses conj (cond-> arg' (= arg arg') (conj ret)))
                            ret)
                          (map? arg)
                          (let [id (or (:as arg) (gensym "ret-id"))]
                            (vswap! vclauses conj (flatten-map arg id))
                            id)
                          :else arg)))
                 args)
        clauses @vclauses]
    (when (seq clauses)
      (conj clauses clause))))

(defn lift-all
  "Expand rules (which may contain nested expressions, ands, ors, nots or freshes) into
   textbook datalog. Supplementary rules mays be created."
  ([rules] (lift-all rules identity))
  ([rules resolve]
    (let [new-rules (atom [])]
      (letfn [(extract-rule! [clauses]
                (let [head (cons (gensym 'pre-or) (into #{} (mapcat used-vars) clauses))]
                  (swap! new-rules conj (cons head clauses))
                  head))
              (lift [aliases done clauses]
                ; MUST returns a seq of vectors (if we have nested laziness 
                ; it will end bad)
                (if-some [[[op & args :as clause] & more-clauses] (seq clauses)]
                  (cond
                    (map? clause)
                    (recur aliases done (cons (flatten-map clause) more-clauses))
                    (identical? lift op) ; sentinel for popping aliases
                    (recur (first args) done more-clauses)
                    (keyword? op)
                    (recur aliases done (cons (expand-kw-clause clause '_) more-clauses))
                    :else
                    (let [op (resolve op)
                          clause (cons op args)]
                      (if (special? op)
                        (case op
                          fresh (let [[fresh-vars & scoped-clauses] args
                                      new-aliases (into aliases (for [v fresh-vars] [v (gensym v)]))]
                                  (recur new-aliases done (concat scoped-clauses
                                                            (cons (list lift aliases) more-clauses))))
                          or (cond
                               (next args)
                               (let [done (case (count done)
                                            (0 1) done
                                            [(extract-rule! done)])]
                                 (mapcat #(lift aliases done (cons % more-clauses)) args))
                               (seq args) ; only 1
                               (recur aliases done (concat args more-clauses))
                               :else nil)
                          and (recur aliases done (concat args more-clauses))
                          not (let [nots (for [clauses (lift aliases [] args)]
                                           (cond
                                             (next clauses)
                                             (list 'not (extract-rule! clauses))
                                             (special? (ffirst clauses))
                                             (let [[op & args] (first clauses)]
                                               (case op
                                                 not args)) ; pretty sure there are edge cases
                                             :else ; only 1
                                             (cons 'not clauses)))]
                                (recur aliases (into done nots) more-clauses)))
                        (if-some [clauses (unnest clause)]
                          (recur aliases done (concat clauses more-clauses))
                          (recur aliases (conj done (map #(aliases % %) clause)) more-clauses)))))
                  [done]))]
        (concat
          (for [[head & clauses] rules
                clauses (lift {} [] clauses)]
            (cons head clauses))
          ; postpone deref until side effects from above are done
          (lazy-seq @new-rules))))))

(defn deps
  "To be used after all lifting is done."
  [rules]
  (reduce
    (fn [m [k v]]
      (update m k (fnil conj #{}) v))
    {}
    (for [[[rel] & clauses] rules
         [op x] clauses]
     [rel (if (= 'not op) (first x) op)])))

(defn negations
  "To be used after all lifting is done."
  [rules]
  (into #{}
    (for [[[rel] & clauses] rules
         [op x] clauses
         :when (= 'not op)]
     [rel (first x)])))

;; stratify
(defn sccs
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

(defn scc-graph [sccs nodes succs]
  (let [node->scc (into {} (for [scc sccs node scc] [node scc]))]
    (reduce
      (fn [m [k v]]
        (update m k (fnil conj #{}) v))
      {}
      (for [scc sccs
           node scc
           :let [from (node->scc node)]
           node' (succs node)
           :let [to (node->scc node')]
           :when (not= from to)]
       [from to]))))

(defn topo-sort [nodes succs]
  (letfn [(xf [rf]
            (let [seen (volatile! #{})]
              (fn self
                ([acc] (rf acc))
                ([acc node]
                  (if (@seen node)
                    acc
                    (do
                      (vswap! seen conj node)
                      (let [acc (reduce self acc (succs node))]
                        (cond-> acc (not (reduced? acc)) (rf node)))))))))]
    (eduction xf nodes)))

(defn stratify
  "To be used after all lifting is done."
  [rules]
  (let [graph (deps rules)
        negations (negations rules)
        sccs (sccs (keys graph) graph)
        _ (doseq [scc sccs a scc b scc :when (negations [a b])]
            (throw (ex-info "Unstratifiable" {:a a :b b})))
        scc-graph (scc-graph sccs (keys graph) graph)
        sorted-sccs (topo-sort sccs scc-graph)
        rules-by-rel (group-by ffirst rules)
        scc-rules (fn [scc]
                    (when-some [rules (seq (mapcat rules-by-rel scc))]
                      (let [recursive? (fn [clauses]
                                         (some (fn [[op x]]
                                                 (case op
                                                   not (recur x)
                                                   (scc op))) clauses))]
                        (group-by (fn [[head & clauses]] (if (recursive? clauses) :recur :init)) rules))))]
    (keep scc-rules sorted-sccs)))

(defn seminaive-stratum
  [{recur-rules :recur init-rules :init}]
  (let [rec-preds (into #{} (map ffirst) recur-rules)
        ; keep only relevant rules
        inc-clauses
        (fn inc-clauses [clauses]
          (when-some [[[op & args :as clause] & more-clauses] (seq clauses)]
            (if (rec-preds op)
              (let [delta-now (cons (cons [:delta op] args)
                                (map (fn self [[op & args :as clause]]
                                       (case op
                                         not (list 'not (self (first args)))
                                         (if (rec-preds op)
                                           (cons [:prev op] args)
                                           clause))) more-clauses))
                    delta-later (inc-clauses more-clauses)]
                (if delta-later
                  [(list 'or (cons 'and delta-now) (list* 'and clause delta-later))]
                  delta-now))
              (some->> (inc-clauses more-clauses) (cons clause)))))
        delta-rules (for [[head & clauses] recur-rules]
                      (cons head (inc-clauses clauses)))
        ; remove ors we just added
        delta-rules (lift-all delta-rules)]
    {:init init-rules
     :delta delta-rules}))

(defprotocol Rel
  (lookup [rel bp] [rel bp tuple]))

#_(extend-protocol Rel
   clojure.lang.APersistentSet
   (lookup [s bp] #(lookup s bp %))
   (lookup [s bp tuple]
     (for [item s
           :when (every? #(= (nth item %) (nth tuple %)) bp)]
       item)))

(defn- match [bindings pat tuple]
  (reduce
    (fn [bindings [x v]]
      (if (symbol? x)
        (if (= '_ x)
          bindings
          (if-some [x (bindings x)] ; no nils
            (if (= x v)
              bindings
              (reduced nil))
            (assoc bindings x v)))
        (if (= x v)
          bindings
          (reduced nil))))
    bindings
    (map vector pat tuple)))

(defn make-db [datascript-db]
  {`datom datascript-db})

(defn eval-rule [db [[head-pred & head-args] & clauses]]
  (letfn [(eval-clause [bindings-seq [pred & args]]
            (case pred
              not (remove #(seq (eval-clause [%] (first args))) bindings-seq)
              call (let [f (first args)
                         args (vec (next args))
                         ret (peek args)
                         args (pop args)]
                     (keep
                       (fn [bindings]
                         (let [r (apply (bindings f f) (map #(bindings % %) args))]
                           (cond
                             (not (symbol? ret))
                             (when (= r ret) bindings)

                             (= '_ ret) bindings

                             (contains? bindings ret)
                             (when (= r (bindings ret)) bindings)

                             :else (assoc bindings ret r))))
                       bindings-seq))
              (let [rel (case pred
                          enlivez.impl.seminaive/datom (d/datoms (db pred) :eavt) ; brutal
                          (db pred))]
                (mapcat (fn [bindings] (keep #(match bindings args %) rel)) bindings-seq))))]
    (map #(map % head-args) (reduce eval-clause [{}] clauses))))

(defn eval-seminaive-stratum [db {init-rules :init delta-rules :delta}]
  (if-not (seq delta-rules)
    (transduce
      (map (fn [[[op] :as rule]]
             {op (set (eval-rule db rule))}))
      (partial merge-with into) db init-rules)
    (let [rec-preds (into #{} (map ffirst) delta-rules)
          db (into db
               (map (fn [op]
                      {op #{}
                       [:prev op] #{}
                       [:delta op] #{}}))
               rec-preds)
          db (transduce
               (map (fn [[[op] :as rule]]
                      (let [rel (set (eval-rule db rule))]
                        {op rel
                         [:delta op] rel})))
               (partial merge-with into) db init-rules)]
      (loop [db db]
        (let [delta-db (transduce
                         (map (fn [[[pred] :as rule]]
                                {pred (into #{} (remove (db pred)) (eval-rule db rule))}))
                         (partial merge-with into) {} delta-rules)
              db (reduce
                   (fn [db pred]
                     (let [rel (db pred)
                           drel (delta-db pred)]
                       (assoc db
                         [:prev pred] rel
                         pred (into rel drel)
                         [:delta pred] drel)))
                   db rec-preds)]
          (if (seq (mapcat delta-db rec-preds))
            (recur db)
            (reduce
              (fn [db pred] (dissoc db [:prev pred] [:delta pred]))
              db rec-preds)))))))

(defn eval-seminaive-strata [db seminaive-strata]
  (reduce eval-seminaive-stratum db seminaive-strata))

(defn eval-rules [db rules]
  (eval-seminaive-strata db (map seminaive-stratum (stratify rules))))

(defn binding-profile [bound-vars [pred & args]]
  (if (= 'not pred)
    (recur bound-vars (first args))
    (into #{} (keep-indexed (fn [i arg] (when (or (not (symbol? arg)) (bound-vars arg)) i))) args)))

(defn used-binding-profiles [rules]
  (transduce
    (map
      (fn [[head & clauses]]
        (first
          (reduce
            (fn [[indexes bound-vars] [pred & args :as clause]]
              [(update indexes pred (fnil conj #{})
                 (binding-profile bound-vars clause))
               (if (= 'not pred)
                 bound-vars
                 (-> bound-vars (into (filter symbol?) args) (disj '_)))] )
           [{} #{}] clauses))))
    (partial merge-with into) {} rules))

(defn unwind [v->u u<-v v<-u u v]
  (loop [v->u (assoc v->u v u) u u]
    (if-some [v (u<-v u)]
      (let [u (v<-u v)]
        (recur (assoc v->u v u) u))
      [u v->u])))

(defn hopcroft-karp
  ([u->vs] (hopcroft-karp (set (keys u->vs)) u->vs))
  ([us u->vs]
    ; v->u is the WIP matching
    ; u<-v and v<-u are the edges traversed so far
    (loop [v->u {} u<-v {} v<-u {} lvl us us us]
      (if-some [[u v] (some (fn [u] (some (fn [v] (when (nil? (v->u v)) [u v])) (u->vs u))) lvl)]
        (let [[u v->u] (unwind v->u u<-v v<-u u v)
              us (disj us u)]
          (recur v->u {} {} us us))
        (if (seq lvl)
          (let [; newly reachable v which already have a matching
                dv<-u (into {} (for [u lvl, v (u->vs u)
                                     :when (and (v->u v) (not (v<-u v)))]
                                 [v u]))
                lvl (map v->u (keys dv<-u))
                v<-u (into v<-u dv<-u)
                u<-v (into {} (for [v (keys dv<-u)] [(v->u v) v]))]
            (recur v->u u<-v v<-u lvl us))
          v->u)))))

(defn index-plan
  "Takes binding profiles (as a set of sets of indices) for a predicate and
   returns an index plan as collection of vector of indices."
  [binding-profiles]
  (let [inclusions (reduce
                     (fn [order a]
                       (assoc order a
                         (-> #{}
                           (into
                             (filter #(every? a %))
                             binding-profiles)
                           (disj a))))
                     {} binding-profiles)
        matching (hopcroft-karp inclusions)
        roots (remove (set (vals matching)) binding-profiles)]
    (map #(into [] (comp (take-while some?) (mapcat sort) (distinct)) (iterate matching %)) roots)))

(defn available-bps
  "For a given plan, returns a map of supported bps to indexing paths."
  [plan]
  (into {}
    (for [path plan
          prefix (iterate pop path)
          :while (seq prefix)]
      [(set prefix) path])))

(defn indexes-conj
  "returns a conj fn (taking a rel and a tuple, returning a rel)
   for the given indexing plan."
  [plan]
  (letfn [(index-assoc [path]
            (if-some [[i & is] (seq path)]
              (let [subassoc (index-assoc is)
                    default (if is {} #{})]
                (fn [index tuple]
                  (let [k (nth tuple i)
                        subindex (get index k default)]
                    (assoc index k (subassoc subindex tuple)))))
              conj))]
    (reduce (fn [further-assocs path]
              (let [f (index-assoc path)]
                (fn [rel tuple]
                  (further-assocs (update rel path f tuple)))))
      identity plan)))

(defn index-lookup
  "returns a lookup fn (taking a rel and a tuple, returning a collection of tuples)
   for the given binding profile and index path (bp and path must be compatible)."
  [bp path]
  (let [ignored (- (count path) (count bp))
        scan (reduce (fn [f _] #(mapcat f (vals %)))
               identity (range ignored))
        lookup (reduce (fn [f i]
                         (fn [index tuple]
                           (some-> (get index (nth tuple i)) (f tuple))))
                 (fn [index _] (scan index)) (drop ignored (rseq path)))]
    (fn [rel tuple]
      (lookup (get rel path) tuple))))

(defn rel ; TODO turns this in a proper collection
  ([plan] ; no empty plan, no empty path
    (let [m (zipmap plan (repeat {}))
          lookups (into {}
                    (for [[bp path] (cons [#{} (first plan)] (available-bps plan))]
                      [bp (index-lookup bp path)]))
          conj (indexes-conj plan)]
      (rel m lookups conj)))
  ([m lookups conj]
    (reify
      #?(:clj clojure.lang.Seqable :cljs ISeqable)
      (#?(:clj seq :cljs -seq) [self] (seq (lookup self #{} nil)))
      #?(:clj clojure.lang.IPersistentCollection :cljs ICollection)
      (#?(:clj cons :cljs -conj)  [_ tuple]
        (rel (conj m tuple) lookups conj))
      #?@(:cljs [IEmptyableCollection] :clj [])
      (#?(:clj empty :cljs -empty) [_] (rel (zipmap (keys m) (repeat {})) lookups conj))
      Rel
      (lookup [rel bp]
        (if-some [lkp (lookups bp)]
          #(lkp m %)
          (throw (ex-info "Unsupported binding profile." {:bp bp :supported-bps (keys lookups)}))))
      (lookup [rel bp tuple]
        (if-some [lkp (lookups bp)]
          (lkp m tuple)
          (throw (ex-info "Unsupported binding profile." {:bp bp :supported-bps (keys lookups)})))))))

(defn clause-xf [bound-vars [pred & args :as clause]]
  (case (first clause)
    not
    (let [subxf (clause-xf bound-vars (first args))]
      (fn [rf db]
        (let [subrf (subxf (fn [_ _] (reduced false)) db)]
          (fn [acc bindings]
            (if (subrf true bindings)
              (rf acc bindings)
              acc)))))
    (let [bp (binding-profile bound-vars clause)
          tuple (object-array (count args))
          args (vec args)
          set-tuple!
          (reduce-kv
            (fn [f i arg]
              (cond
                (bound-vars arg)
                (fn [bindings]
                  (f bindings)
                  (aset tuple i (bindings arg)))
                (symbol? arg) f
                :else ; constant
                (fn [^objects tuple bindings]
                  (f bindings)
                  (aset tuple i arg))))
            identity args)
          outs (reduce-kv
                 (fn [m i arg]
                   (if (and (symbol? arg) (not= '_ arg) (not (bound-vars arg)))
                     (assoc m arg (conj m arg []) i)
                     m))
                 {} args)
          outf (reduce-kv
                 (fn [f var [i & is]]
                   (fn [bindings tuple]
                     (let [val (nth tuple i)]
                       (when (every? #(= val (nth tuple %)) is)
                         (f (assoc bindings var val))))))
                 (fn [bindings tuple] bindings)
                 outs)]
      ; TODO eq constraints when same var appears twice
      (fn [rf db]
        (let [lkp (lookup (db pred) bp)]
          (fn [acc bindings]
            (set-tuple! bindings)
            (if-some [bindings (outf bindings )]
              (reduce
                (fn [acc tuple]
                  (if-some [bindings (outf bindings tuple)]
                    (rf acc bindings)
                    acc))
                acc (lkp tuple)))))))))

#_(defn eval-rule [db [[pred & head-args] & clauses]]
   (let [xfs
         (first
           (reduce
             (fn [[xfs bound-vars] clause]
               [(conj xfs (clause-xf bound-vars clause))
                (-> bound-vars (into (filter symbol?) (next clause)) (disj '_))])
             [[] #{}] clauses))]
     (eduction
       (fn [rf]
         (reduce (fn [rf xf] (xf rf db))
           (fn [acc bindings]
             (rf acc (into [] (map bindings) head-args))) (rseq xfs)))
       [{}])))


(comment
  => (index-plan [#{1} #{2} #{1 2} #{1 3} #{1 2 3}])
  ([1 3 2] [2 1]))