(ns enlivez.impl.seminaive)

(defn- TODO [s]
  (throw (ex-info (str "TODO: " s) {})))

(def reserved? '#{or and not fresh let new if when})

(defn used-vars
  [[op & args]]
  (if (reserved? op)
    (case op
      fresh (let [[new-vars & args] args]
              (remove (set new-vars) (mapcat used-vars args)))
      (not and or) (mapcat used-vars args))
    (filter #(and (symbol? %) (not= '_ %)) args)))

;; ok the goal here is to implement seminaive evaluation for a datalog program

;; in order to get to textbook datalog, we need to perform the following steps:
;; 1. remove freshes
;; 2. remove ors (and remove complex not bodies)

(defn lift-freshes
  "Remove freshes by renaming vars."
  [rules]
  (letfn [(lift [[op & args] aliases]
            (if (reserved? op)
              (case op
                fresh (let [[fresh-vars & args] args
                            aliases (into aliases (map (fn [v] [v (gensym v)])) fresh-vars)]
                        (cons 'and (map #(lift % aliases) args)))
                (and or not) (cons op (map #(lift % aliases) args)))
              (cons op (map #(aliases % %) args))))]
    (for [[head & clauses] rules]
      (cons head (map #(lift % {}) clauses)))))

(defn lift-ors
  "Removes ors and complex nots (which somehow are ors -- think De Morgan)"
  [rules]
  (let [new-rules (atom [])]
    (letfn [(extract-rule! [clauses]
              (let [head (cons (gensym 'pre-or) (into #{} (mapcat used-vars) clauses))]
                (swap! new-rules conj (cons head clauses))
                head))
            (lift [done clauses]
              ; MUST returns a seq of vectors (if we have nested laziness 
              ; it will end bad)
              (if-some [[[op & args :as clause] & more-clauses] (seq clauses)]
                (if (reserved? op)
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
                                       (reserved? (ffirst clauses))
                                       (let [[op & args] (first clauses)]
                                         (case op
                                           not args))
                                       :else ; only 1
                                       (cons 'not clauses)))]
                          (recur (into done nots) more-clauses)))
                  (recur (conj done clause) more-clauses))
                [done]))]
      (concat
        (for [[head & clauses] rules
              clauses (lift [] clauses)]
          (cons head clauses))
        ; postpone deref until side effects from above are done
        (lazy-seq @new-rules)))))

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
        delta-rules (lift-ors delta-rules)]
    {:init init-rules
     :delta delta-rules}))

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

(defn eval-rule [db [[op & head-args] & clauses]]
  (letfn [(eval-clause [bindings-seq [op & args]]
            (case op
              not (remove #(seq (eval-clause [%] (first args))) bindings-seq)
              (let [rel (db op)]
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

(defn unwind [v->u u<-v v<-u u v]
  (loop [v->u (assoc v->u v u) u u]
    (if-some [v (u<-v u)]
      (let [u (v<-u v)]
        (recur (assoc v->u v u) u))
      [u v->u])))

(defn hopcroft-karp
  ([u->vs] (hopcroft-karp (set (keys u->vs)) u->vs))
  ([us u->vs]
    (loop [v->u {} u<-v {} v<-u {} lvl us us us]
      (if-some [[u v] (some (fn [u] (some (fn [v] (when (nil? (v->u v)) [u v])) (u->vs u))) lvl)]
        (let [[u v->u] (unwind v->u u<-v v<-u u v)
              us (disj us u)]
          (recur v->u {} {} us us))
        (if (seq lvl)
          (let [dv<-u (into {} (for [u lvl v (u->vs u) :when (-> v v->u u<-v nil?)] [v u]))
               lvl (map v->u (vals dv<-u))
               v<-u (into v<-u dv<-u)
               u<-v (into {} (for [v (keys dv<-u)] [(v->u v) v]))]
           (recur v->u u<-v v<-u lvl us))
          v->u)))))


 