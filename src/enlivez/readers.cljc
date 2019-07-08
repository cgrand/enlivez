(ns enlivez.readers)

(defn ent [m-or-s]
  (into {}
    (for [[k v] (if (map? m-or-s) m-or-s (partition 2 m-or-s))]
      (if (and (keyword? v) (= "attrs" (name v)))
        (into {}
          (for [k k]
            [(keyword (or (namespace k) (namespace v)) (name k)) (symbol (name k))]))
        [k v]))))

(defn attrs [s]
  (reduce
    (fn [attrs x]
      (if (vector? x)
        (let [ns (name (peek attrs))
              attrs (pop attrs)]
          (into attrs (for [attr x]
                        (cond
                          (symbol? attr) (symbol ns (name attr))
                          (keyword? attr) (keyword ns (name attr))
                          :else attr))))
        (conj attrs x)))
    [] s))