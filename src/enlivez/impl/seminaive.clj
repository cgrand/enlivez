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

(defn seminaive-step
  [rules scc]
  (let [; keep only relevant rules
        rules (filter (fn [[[op]]] (scc op)) rules)
        recursive? (fn [clauses]
                     (some (fn [[op x]]
                             (case op
                               not (recur x)
                               (scc op))) clauses))
        seed-rules (remove (fn [[head & clauses]] (recursive? clauses))  rules)
        rec-rules (filter (fn [[head & clauses]] (recursive? clauses))  rules)
        inc-clauses
        (fn inc-clauses [clauses]
          (when-some [[[op & args :as clause] & more-clauses] (seq clauses)]
            (if (scc op)
              (let [delta-now (cons (cons [:delta op] args)
                                (map (fn self [[op & args :as clause]]
                                       (case op
                                         not (list 'not (self (first args)))
                                         (if (scc op)
                                           (cons [:prev op] args)
                                           clause))) more-clauses))
                    delta-later (inc-clauses more-clauses)]
                (if delta-later
                  [(list 'or (cons 'and delta-now) (list* 'and clause delta-later))]
                  delta-now))
              (some->> (inc-clauses more-clauses) (cons clause)))))
        delta-rules (for [[head & clauses] rec-rules]
                      (cons head (inc-clauses clauses)))
        ; remove ors we just added
        delta-rules (lift-ors delta-rules)]
    {:seed seed-rules
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

(defn eval-naive-step [db {:keys [seed delta]}]
  (let [rec-rels (into #{} (map ffirst) delta)
        db (into db
             (map (fn [op]
                    {op #{}
                     [:prev op] #{}
                     [:delta op] #{}}))
             rec-rels)
        db (transduce
             (map (fn [[[op] :as rule]]
                    (let [rel (set (eval-rule db rule))]
                      {op rel
                       [:delta op] rel})))
             (partial merge-with into) db seed)]
    (loop [db db]
      (let [delta-db (transduce
                       (map (fn [[[op] :as rule]]
                              {op (set (eval-rule db rule))}))
                       (partial merge-with into) {} delta)
            db (reduce
                 (fn [db op]
                   (let [rel (db op)
                         drel (remove rel (delta-db op))]
                     (assoc db
                       [:prev op] rel
                       op (into rel drel)
                       [:delta op] drel)))
                 db rec-rels)]
        (if (seq (mapcat #(db [:delta %]) rec-rels))
          (recur db)
          (reduce
            (fn [db op] (dissoc db [:prev db] [:delta db]))
            db rec-rels))))))

(defn scc-kind [scc rules-by-name sccs-graph]
  (let [n (reduce
           (fn [m n]
             (case n
               3 (reduced 3)
               (max m n)))
           0
           (for [rule-name scc
                 [_ & body] (rules-by-name rule-name)]
             (reduce
               (fn [n [op x]]
                 (if (= 'not op)
                   (if (scc (first x))
                     (reduced 3)
                     n)
                   (if (scc op)
                     (min 2 (inc n))
                     n)))
               0
               body)))]
    (case n
      0 :acyclic-singleton
      1 :linear
      2 :non-linear
      3 :non-stratified-negation)))
