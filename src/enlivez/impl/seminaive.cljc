(ns enlivez.impl.seminaive
  (:require [datascript.core :as d]))

(defn- TODO [s]
  (throw (ex-info (str "TODO: " s) {})))

(def special? '#{entity or and not let #_new #_if #_when})
(def special-pred? #{`datom 'eq})

;; ok the goal here is to implement seminaive evaluation for a datalog program

(defn flatten-map
  "Returns a seq of clauses."
  ([clause]
    (let [id (or (:db/id clause) (gensym 'id))]
      (flatten-map clause id)))
  ([clause id]
    (cons 'and
      (for [[k v] (dissoc clause :db/id)]
        (list k id v)))))

(defn expand-kw-clause
  [[k & args]]
  (if (.startsWith (name k) "_")
    (let [k (keyword (namespace k) (subs (name k) 1))]
      (case (count args)
;        1 (list `datom '% k (nth args 0))
        2 (list `datom (nth args 1) k (nth args 0))
        3 (list `datom (nth args 1) k (nth args 0) (nth args 2))))
    (case (count args)
;      1 (list `datom (nth args 0) k '%)
      2 (list `datom (nth args 0) k (nth args 1))
      3 (list `datom (nth args 0) k (nth args 1) (nth args 2)))))

(defn- explicitize-kw [[k & args] ret]
  (let [args' (map (fn [x] ({'% ret} x x)) args)]
    (if (= args args')
      (expand-kw-clause (cons k (concat args' [ret])))
      (expand-kw-clause (cons k args')))))

(defn- explicitize-entity [avs ret]
  (let [avs (partition 2 avs)
        avs' (map (fn [[a v]] [({:db/id 'eq} a a) ({'% ret} v v)]) avs)
        has-ret (not= avs avs')
        avs (cond->> avs'
              (not= 'eq (ffirst avs')) (cons (list 'eq (if has-ret (gensym "eid") ret))))
        [[_ e] & avs] avs]
    (cons 'and (map (fn [[a v]]
                      (if (seq? a)
                        (let [[op & args] a] ; splice
                          (concat (list* op e args) [v]))
                        (list a e v))) avs))))

(defn- explicitize-return [[op & args :as expr] ret]
  (case op
    or (cons 'or (map #(explicitize-return % ret) args))
    and (concat (cons 'and (map #(explicitize-return % (gensym "_")) (butlast args))) [(explicitize-return (last args) ret)])
    not (list 'and
          (cons 'not (map #(explicitize-return % (gensym "_")) args))
          (list 'eq ret true))
    entity (explicitize-entity (next expr) ret)
    (let [expr (cond-> expr (keyword? (first expr)) (explicitize-kw '%))
         expr' (map (fn [x] ({'% ret} x x)) expr)]
     (cond-> expr' (= expr expr') (concat [ret])))))

(defn- expand-entity [avs]
  (let [avs (map (fn [[a v]] [({:db/id 'eq} a a) v]) (partition 2 avs))
        avs (cond->> avs
              (not= 'eq (ffirst avs)) (cons (list 'eq (gensym "eid"))) )
        [[_ e] & avs] avs]
    (cons 'and
      (map (fn [[a v]]
             (if (seq? a)
               (let [[op & args] a] ; splice
                 (concat (list* op e args) [v]))
               (list a e v))) avs))))

(defn used-vars
  "Returns vars used in a canonical (lifted) clause."
  [[op & args :as clause]]
  (case op
    not (recur (first args))
    (filter symbol? args)))

(defn expand-clause [clause]
  (cond
    (seq? clause)
    (let [[op] clause]
      (cond
        (keyword? op) (expand-kw-clause clause)
        (= 'entity op) (expand-entity (next clause))
        :else clause))
    (vector? clause) (cons `vector clause)
    (map? clause) (cons `hash-map (mapcat seq clause))
    (set? clause) (cons `hash-set clause)
    :else (throw (ex-info (str "Unexpected clause type: " clause) {:clause clause}))))

(defn unnest
  "If clause has nested expressions then unnest them (not recursively) else nil."
  [[pred & args]]
  (let [vclauses (volatile! [])
        clause (cons pred
                 (doall
                   (map (fn [arg]
                         (if (coll? arg)
                           (let [arg (if (seq? arg) arg (expand-clause arg))
                                 ret (gensym "ret")]
                             (vswap! vclauses conj
                               (case (first arg)
                                 or (cons 'or
                                      (map #(explicitize-return % ret) (next arg))) 
                                 and
                                 (let [last-i (- (count arg) 2)] ; 2 is 1 for the first and 1 for the last
	                                   (cons 'and
	                                     (map-indexed 
	                                       (fn [i v]
	                                         (cond
	                                           (seq? v)
	                                           (case (first v)
	                                             not v
	                                             (explicitize-return v
	                                               (if (< i last-i) '_ ret)))
	                                           (= i last-i) (list 'eq v ret)
	                                           :else
	                                           (throw (ex-info (str "Unexpected expression in tail position of an and: " v) {:v v}))))
	                                      (next arg))))
                                 ; else
                                 (explicitize-return arg ret)))
                             ret)
                           arg))
                     args)))
        clauses @vclauses]
    (when (seq clauses)
      (conj clauses clause))))

(defn lift-all
  "Expand rules (which may contain nested expressions, ands, ors, nots) into
   textbook datalog. Supplementary rules mays be created."
  ([rules] (lift-all rules identity))
  ([rules resolve]
    (let [new-rules (atom [])]
      (letfn [(extract-rule! [clauses]
                (let [head (cons (gensym 'pre-or) (into #{} (mapcat used-vars) clauses))]
                  (swap! new-rules conj (cons head clauses))
                  head))
              (lift [done clauses]
                ; MUST returns a seq of vectors (if we have nested laziness 
                ; it will end bad)
                (if-some [[clause & more-clauses] (seq clauses)]
                  (let [[op & args] (expand-clause clause)
                        op (resolve op)
                        clause (cons op args)]
                    (if (special? op)
                      (case op
                        or (cond
                             (next args)
                             (let [done (case (count done)
                                          (0 1) done
                                          [(extract-rule! done)])]
                               (mapcat #(lift done (cons % more-clauses)) args))
                             (seq args) ; only 1
                             (recur done (concat args more-clauses))
                             :else nil)
                        and (recur done (concat args more-clauses))
                        not (let [nots (for [clauses (lift [] args)]
                                         (cond
                                           (next clauses)
                                           (list 'not (extract-rule! clauses))
                                           (special? (ffirst clauses))
                                           (let [[op & args] (first clauses)]
                                             (case op
                                               not args)) ; pretty sure there are edge cases
                                           :else ; only 1
                                           (cons 'not clauses)))]
                              (recur (into done nots) more-clauses)))
                      (if-some [clauses (unnest clause)]
                        (recur done (concat clauses more-clauses))
                        (recur (conj done (map #(if (= '_ %)
                                                  (gensym '_)
                                                  %) clause)) more-clauses))))
                  [done]))]
        (concat
          (let [ret (gensym "ret")]
            (for [[head & clauses] rules
                  :let [head' (map (fn [x] ({'% ret} x x)) head)
                        clauses (if (= head head')
                                  clauses
                                  [(list 'eq (cons 'and clauses) ret)])]
                  clauses (lift [] clauses)]
             (cons head' clauses)))
          ; postpone deref until side effects from above are done
          (lazy-seq @new-rules))))))

(defn rules-deps
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
  "Returns the strongly connected components (as a set of sets)
   of a graph specified by its nodes and a successor function succs
   from node to nodes.
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
  (let [graph (rules-deps rules)
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
        (if-some [x (bindings x)] ; no nils
          (if (= x v)
            bindings
            (reduced nil))
          (assoc bindings x v))
        (if (= x v)
          bindings
          (reduced nil))))
    bindings
    (map vector pat tuple)))

(defn make-db [datascript-db]
  {`datom datascript-db})

(defn eval-rule [db [[head-pred & head-args] & clauses]]
  (letfn [(eval-clause [bindings-seq [pred & args :as clause]]
            (case pred
              not (remove #(seq (eval-clause [%] (first args))) bindings-seq)
              call (let [f (first args)
                         args (vec (next args))
                         ret (peek args)
                         args (pop args)
                         bound (fn [bindings x]
                                 (if (symbol? x)
                                   (let [x' (bindings x bindings)]
                                     (if (identical? x' bindings)
                                       (throw (ex-info "Insufficient bindings"
                                                {:clause clause :var x}))
                                       x'))
                                   x))]
                     (keep
                       (fn [bindings]
                         (let [r (apply (bound bindings f) (map #(bound bindings %) args))]
                           (cond
                             (not (symbol? ret))
                             (when (= r ret) bindings)

                             (contains? bindings ret)
                             (when (= r (bindings ret)) bindings)

                             :else (assoc bindings ret r))))
                       bindings-seq))
              eq (let [[a b] args]
                   (if (symbol? a)
                     (if (symbol? b)
                       (keep
                         (fn [bindings]
                           (let [av (bindings a bindings)
                                 bv (bindings b bindings)]
                             (if (identical? av bindings)
                               (if (identical? bv bindings)
                                 (throw (ex-info "Insufficient bindings" {:clause clause}))
                                 (assoc bindings a bv))
                               (if (identical? bv bindings)
                                 (assoc bindings b av)
                                 (when (= av bv) bindings)))))
                         bindings-seq)
                       (keep
                         (fn [bindings]
                           (let [av (bindings a bindings)]
                             (if (identical? av bindings)
                               (assoc bindings a b)
                               (when (= av b) bindings))))
                         bindings-seq))
                     (if (symbol? b)
                       (keep
                         (fn [bindings]
                           (let [bv (bindings b bindings)]
                             (if (identical? bv bindings)
                               (assoc bindings b a)
                               (when (= a bv) bindings))))
                         bindings-seq)
                       (when (= a b) bindings-seq))))
              (case pred
                enlivez.impl.seminaive/datom ; brutal & assumes attr is known
                (let [rel (d/datoms (db pred) :aevt (second args))]
                  (case (count args)
                    3 (let [[e a v] args]
                        (mapcat (fn [bindings]
                                  (keep #(match bindings args %)
                                    (if (or (not (symbol? e)) (contains? bindings e))
                                      (d/datoms (db pred) :aevt a (bindings e e))
                                      (d/datoms (db pred) :aevt a)))) bindings-seq))
                    4 (let [[e a default v] args
                            args [e a v]]
                        (mapcat
                          (fn [bindings]
                            (when-not (and (contains? bindings e)
                                        (or (not (symbol? default)) (contains? bindings default)))
                              (throw (ex-info "insufficient bindings" {:clause (list pred e a default v)})))
                            (if-some [datoms (seq (d/datoms (db pred) :aevt a (bindings e e)))]
                              (seq (keep #(match bindings args %) datoms))
                              (let [default (bindings default default)]
                                (if (symbol? v)
                                  (if (contains? bindings v)
                                    (when (= (bindings v) default)
                                      [bindings])
                                    [(assoc bindings v default)])
                                  (when (= v default) [bindings])))))
                          bindings-seq))))
                (let [rel (db pred)]
                  (mapcat (fn [bindings]
                            (keep #(match bindings args %) rel)) bindings-seq)))))]
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
                      {op (db op #{})
                       [:prev op] #{}
                       [:delta op] (db op #{})}))
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

(defn prepare-rules [rules]
  (into [] (map seminaive-stratum) (stratify rules)))

(defn eval-prepared-rules [db prepared-rules]
  (eval-seminaive-strata db prepared-rules))

(defn eval-rules [db rules]
  (eval-prepared-rules db (prepare-rules rules)))

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
               (cond-> bound-vars
                 (not= pred 'not) (into (filter symbol?) args))] )
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
                   (if (and (symbol? arg) (not (bound-vars arg)))
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

;; computing keyset from clauses

(defn var-deps1 
  "returns a sequence of symbols pairs where the key sets the value
   (e.g. cardinality one).
   :known is a special key "
  [[op & args] card1? uniq?]
  (case op
    not nil
    call (let [ret (last args)] ; is this right
           (zipmap (butlast args) (repeat ret)))
    enlivez.impl.seminaive/datom
    (let [[e a v] args]
      (if (keyword? a)
        (cond
          (symbol? e)
          (if (symbol? v)
            (if (card1? a)
              [[e v]]
              [[e e]
               [v v]])
            (if (uniq? a)
              [[:known e]]
              [[e e]]))
          (symbol? v) ; and not symbol? e
          (when-not (card1? a)
            [[v v]]))
        (throw (ex-info "Unsupported dynamic attribute." {:a a}))))
    ; don't try going down rules at the moment
    (zipmap args args)))

#_(defn- deps [conjunction card1? uniq?]
   (transduce (mapcat
               (fn self [clause]
                 (if (seq? clause) 
                   (case (first clause)
                     ; emit nothing on not: imagine (not [?a :ident/attr :k])
                     (not not=) nil
                     = (let [syms (filter symbol? (next clause))]
                         (for [a syms, b syms
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

(defn- keyset [clauses schema known-vars]
  (let [card1? #(= :db.cardinality/one (get-in schema [% :db/cardinality] :db.cardinality/one))
        uniq? #(some-> schema (get %) :db/unique)
        succs (transduce (mapcat #(var-deps1 % card1? uniq?))
                (fn 
                  ([succs] succs)
                  ([succs [k v]]
                    (assoc succs k (conj (succs k #{}) v))))
                {:known (set known-vars)}
                clauses)
        sccs (sccs (keys succs) succs)
        scc-of (into {}
                 (for [scc sccs, var scc]
                   [var scc]))
        key-sccs (transduce (comp cat (map scc-of)) disj (disj sccs #{:known}) (vals succs))]
    key-sccs))

(defn keyvars [bodies schema known-vars]
  (into #{}
    (comp
      (mapcat #(keyset % schema known-vars))
      (map first))
    bodies))
