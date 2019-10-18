(ns enlivez.impl.magic)

(defn addorn-clause [[pred & args] env]
  (case pred
    not [(first (addorn-clause (first args) env)) env]
    [(cons (into [pred] (map #(or (not (symbol? %)) (env % false))) args) args)
     (transduce (filter symbol?)
       (fn
         ([env] env)
         ([env arg] (assoc env arg true))) env args)]))

(defn addorn-rules
  [rules goals]
  (let [rules-by-name (group-by ffirst rules)]
    (loop [addorned-rules []
           done #{}
           todo (into #{}
                  (for [goal goals [[op & args :as head]] (rules-by-name goal)]
                    (into [op] (map (constantly false)) args)))]
      (if-some [[pred & bp :as addorned-pred] (first todo)]
        (let [newly-addorned-rules
              (for [[[_ & args] & clauses] (rules-by-name pred)]
                (cons
                  (cons addorned-pred args)
                  (first
                    (reduce 
                      (fn [[addorned-clauses bound-vars] clause]
                        (let [[addorned-clause bound-vars] (addorn-clause clause bound-vars)]
                          [(conj addorned-clauses addorned-clause) bound-vars]))
                      [[] (zipmap args bp)] clauses))))
              addorned-preds
              (for [[_ & clauses] newly-addorned-rules
                    [op & args] clauses]
                (case op
                  not (ffirst args)
                  op))]
          (recur
            (into addorned-rules newly-addorned-rules)
            (conj done addorned-pred)
            (-> todo (into (remove done) addorned-preds) (disj addorned-pred))))
        addorned-rules))))

(defn magic-clause
  "when at least one arg bound, returns the matching magic-clause, else nil."
  [[op & args] idb-preds]
  (case op
    not (recur (first args) idb-preds)
    (let [[pred & bp :as addorned-pred] op]
      (when (and (idb-preds addorned-pred) (some true? bp))
        (cons
          [:magic addorned-pred]
          (remove nil? (map #(when %1 %2) bp args)))))))

(defn unaddorn [[op & args]]
  (case op
    not (list 'not (unaddorn (first args)))
    (cons (first op) args)))

(defn magic-rules [addorned-rule idb-preds]
  (let [[head & clauses] addorned-rule
        mclause (magic-clause head idb-preds)
        prev-clauses (cond-> [] mclause (conj mclause))
        head (cond-> head (nil? mclause) unaddorn)
        [clauses new-rules] (reduce (fn [[prev-clauses new-rules] clause]
                                      ; TODO: factor prefix queries out
                                      (if-some [mhead (magic-clause clause idb-preds)]
                                        [(conj prev-clauses clause) (conj new-rules (cons mhead prev-clauses))]
                                        [(conj prev-clauses (unaddorn clause)) new-rules]))
                              [prev-clauses []] clauses)]
    (cons (cons head clauses) new-rules)))

(defn magic-rewrite
  "Rewrites rules while preserving the computation of goals.
   rules is a collection of canonical rules.
   goals is a collection of rule names."
  [rules goals]
  (let [addorned-rules (addorn-rules rules goals)
        idb-preds (into #{} (map ffirst) addorned-rules)]
    (concat #_bridge-rules (mapcat #(magic-rules % idb-preds) addorned-rules))))
