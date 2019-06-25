(ns enlivez.q)

(defn pow [choices n]
    (if (pos? n)
      (for [v (pow choices (dec n))
            choice choices]
        (conj v choice))
      [[]]))

(defn best-suited-index [[e a v] avet-enabled]
  (let [m (cond-> {:eavt [e a v]
                   :aevt [a e v]}
            avet-enabled (assoc :avet [a v e]))]
    (key (first (sort-by (fn [[index sig]] 
                           (conj
                             (mapv #(case % (\i \v) 0 \o 1 \_ 2) sig)
                             (case index
                               :eavt 0
                               :aevt 1
                               :avet 2)))
                  compare m)))))

(defmacro pattern-xforms-array []
  (letfn
    [(emit-reduce [profile avet-enabled]
       (let [index (best-suited-index profile avet-enabled)
             modes (into {} (map vector '[e a v] profile))
             outs (keep (fn [[arg p]] (case p \o arg nil)) modes)
             args-in-index-order (->> index name (take 3) (map #(symbol (str %))))
             datoms-args
             (->> args-in-index-order
               (map (fn [arg]
                      (case (modes arg)
                        \i `(aget ~'ctx ~arg)
                        \v arg
                        nil)))
               (take-while some?))
             check-valid-e (->> args-in-index-order
                             (map (fn [arg]
                                    (case (modes arg)
                                      \i arg
                                      \v '_
                                      nil)))
                             (take-while some?)
                             (some #{'e}))
             filters (->> args-in-index-order (drop (count datoms-args))
                       (keep (fn [arg]
                               (let [prop (symbol (str ".-" arg))]
                                 (case (modes arg)
                                   \i `(= (~prop ~'datom) (aget ~'ctx ~arg))
                                   \v `(= (~prop ~'datom) ~arg)
                                   nil)))))
             body `(do
                     ~@(for [out outs
                             :let [prop (symbol (str ".-" out))]]
                         `(aset ~'ctx ~out (~prop ~'datom)))
                     ~'(rf acc ctx))
             body (if (seq filters) ; TODO, warn on filters
                    `(if (and ~@filters)
                       ~body
                       ~'acc)
                    body)
             reduce-form
             `(reduce
                (fn [~'acc ~'datom] ~body)
                ~'acc
                (->>
                  (datascript.core/datoms (aget ~'ctx ~'db) ~index
                   ~@datoms-args)
                  ~@(when check-valid-e ; wrap above call in below when-not
                     [`(when (maybe-a-ref? (aget ~'ctx ~'e)))])))
             #_#_reduce-form
             `(do
                (prn 'datoms ~index ~@datoms-args)
                (if ~(some? check-valid-e) (prn 'check-valid-e '~index '~profile))
                ~reduce-form)]
         (cond
           (not= :avet index) reduce-form
           (#{\v \i} (modes 'a))
           `(if (indexed-attr? (aget ~'ctx ~'db) ~(case (modes 'a) \v 'a \i `(aget ~'ctx ~'a)))
              ~reduce-form
              ~(emit-reduce profile false))
           :else
           (emit-reduce profile false))))]
    `(cljs.core/array
      ~@(for [profile (pow "vio_" 3)]
          `(fn ~'[db e a v]
             (fn ~'[rf]
               (fn ~'[acc ctx]
                 ~(emit-reduce profile true))))))))

