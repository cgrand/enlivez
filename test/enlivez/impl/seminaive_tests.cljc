(ns enlivez.impl.seminaive-tests
  #?(:clj
     (:use [clojure.test :only [deftest is are]])
     :cljs
     (:use-macros [cljs.test :only [deftest is]]))
  (:require
    [enlivez.impl.seminaive :as impl]
    [datascript.core :as d]))

(defn eq-rule? "tests whether two expansions are equivalent"
  [a b]
  (letfn [(eq? [eqs a b]
            (cond
              (and (sequential? a) (sequential? b) (= (count a) (count b)))
              (reduce (fn [eqs [a b]] (or (eq? eqs a b) (reduced nil)))  eqs (map vector a b))
              (and (symbol? a) (symbol? b))
              (cond
                (eqs a) (when (= (eqs b) a) eqs)
                (eqs b) nil
                :else (-> eqs (assoc a b) (assoc b a)))
              (= a b) eqs))]
    (eq? {} a b)))

(defn eq-rules? [as bs]
  (= #{}
     (reduce
      (fn [as b]
        (or (some->> (some #(when (eq-rule? b %) %) as) (disj as))
            (reduced nil)))
      (set as) bs)))

(deftest lifting
  (is (= (set (impl/lift-all
                '[([rsg x y] (or [flat x y]
                               (and [up x x1] [rsg y1 x1] [down y1 y])))]))
        '#{([rsg x y] [flat x y])
           ([rsg x y] [up x x1] [rsg y1 x1] [down y1 y])}))
  (are [a b] (eq-rules? (impl/lift-all a) b)
    ; nesting
    '[((anc x a) (or (parent x a)
                   (parent (anc x) a)))]
    '[((anc x a) (parent x a))
      ((anc x a) (anc x ret49179) (parent ret49179 a))]
    ; entities
    '[[(agent eid) (entity :db/id eid :first-name "james" :last-name "bond")]]
    '(((agent eid) (enlivez.impl.seminaive/datom eid :first-name "james") (enlivez.impl.seminaive/datom eid :last-name "bond")))
    ; expression bodies
    '[[(agent %) (entity :first-name "james" :last-name "bond")]]
    '(((agent ?) (enlivez.impl.seminaive/datom ?e :first-name "james") (enlivez.impl.seminaive/datom ?e :last-name "bond") (eq ?e ?)))
    ; nested entities
    '[[(bond-car model plate)
       (entity
         :car/owner (entity :first-name "james" :last-name "bond")
         :car/model model
         :car/plate plate)]]
    '(((bond-car model plate)
        (enlivez.impl.seminaive/datom ?bond :first-name "james")
        (enlivez.impl.seminaive/datom ?bond :last-name "bond")
        (enlivez.impl.seminaive/datom ?car :car/owner ?bond)
        (enlivez.impl.seminaive/datom ?car :car/model model)
        (enlivez.impl.seminaive/datom ?car :car/plate plate)))
    ; nested-entities + rev attribute (bad query btw)
    '[[(bond-car model plate)
       (entity :first-name "james" :last-name "bond"
         :car/_owner (entity :car/model model
                       :car/plate plate))]]
    '(((bond-car model plate)
       (enlivez.impl.seminaive/datom ?bond :first-name "james")
       (enlivez.impl.seminaive/datom ?bond :last-name "bond")
       (enlivez.impl.seminaive/datom ?car :car/model model)
       (enlivez.impl.seminaive/datom ?car :car/plate plate)
       (enlivez.impl.seminaive/datom ?car :car/owner ?bond)))
    ; nested ors
    '[[(x a b c) (f a (or (g b) (h c)))]]
    '(((x a b c) (g b ?0) (f a ?0))
      ((x a b c) (h c ?0) (f a ?0)))
    ; only the last attribute of a nested and matters (like in Clojure)
    '[[(x a b c) (f a (and (g b) (h c)))]]
    '(((x a b c) (g b ?0) (h c ?1) (f a ?1)))
    ; last argument of a nested and can even be a symbol! (you can then put a not before)
    '[[(x a b c) (f a (and (g b) (h c) (not (bad c)) c))]]
    '(((x a b c) (g b ?0) (h c ?1) (not (bad c)) (eq c ?2) (f a ?2)))))

(def rsg-edb '{up #{[a e] [a f] [f m] [g n] [h n] [i o] [j o]}
   flat #{[g f] [m n] [m o] [p m]}
   down #{[l f] [m f] [g b] [h c] [i d] [p k]}})

(deftest rsg
  (is (= ('rsg (impl/eval-rules
                 rsg-edb
                 '[([rsg x y] [flat x y])
                   ([rsg x y] [up x x1] [rsg y1 x1] [down y1 y])]))
        '#{(j f) (h f) (m n) (g f) (a d) (p m) (a b) (f k) (a c) (i f) (m o)})))

(deftest datascript-edb
  (let [db (-> (d/empty-db {:up {:db/valueType :db.type/ref
                                 :db/cardinality :db.cardinality/many}
                            :flat {:db/valueType :db.type/ref
                                   :db/cardinality :db.cardinality/many}
                            :down {:db/valueType :db.type/ref
                                   :db/cardinality :db.cardinality/many}})
             (d/db-with
               (concat
                 (for [[pred tuples] rsg-edb
                       [a b] tuples]
                   [:db/add (str a) (keyword pred) (str b)])
                 (distinct (for [[pred tuples] rsg-edb
                                 tuple tuples
                                 item tuple]
                             [:db/add (str item) :db/ident (keyword item)])))))]
    (is (= ('? (impl/eval-rules
                 (impl/make-db db)
                 (impl/lift-all
                   '[([? x' y'] (rsg x y) (:db/ident x x') (:db/ident y y'))
                     ([rsg x y] ;-
                       (or (:flat x y) (rsg (:_down y) (:up x))))])))
          '#{(:j :f) (:h :f) (:m :n) (:g :f) (:a :d) (:p :m) (:a :b) (:f :k) (:a :c) (:i :f) (:m :o)}))
    (is (= ('? (impl/eval-rules
                 (impl/make-db db)
                 (impl/lift-all
                   '[([? x' d] (:db/ident x x') (:down x "-" d))])))
          '#{(:a "-") (:b "-") (:d "-") (:i 14) (:l 4) (:h 12) (:e "-") (:c "-") (:m 4) (:g 16) (:k "-") (:p 13) (:j "-") (:f "-") (:o "-") (:n "-")}))
    (is (= ('? (impl/eval-rules
                 (impl/make-db db)
                 (impl/lift-all
                   '[([? x'] (:db/ident x x') (:down x "-" "-"))])))
          '#{(:e) (:b) (:n) (:o) (:c) (:f) (:k) (:a) (:j) (:d)}))))

(deftest fnrel
  (let [r (impl/rel [[1 0]])
        r (into r [[1 2 3] [4 5 6] [8 2 9]])]
    (is (= (set r) #{[1 2 3] [4 5 6] [8 2 9]}))
    (is (= (set (impl/lookup r #{1} [nil 2 nil])) #{[1 2 3] [8 2 9]}))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
          #"Unsupported binding profile"
          (set (impl/lookup r #{0} [2 nil nil]))))))

(deftest calling-fp
  (is (= '#{([:c :d]) ([:a :c :d]) ([:a :c]) ([:a :b])}
        (`lineage (impl/eval-rules
                    `{parent #{[:a :b] [:a :c] [:c :d]}}
                    (impl/lift-all
                      `[[(anc x y p) (parent x y) (~'call ~vector x y p)]
                        [(anc x y p) (anc x z p') (parent z y) (~'call ~conj p' y p)]
                        [(lineage p) (anc ~'_ ~'_ p)]]))))))

