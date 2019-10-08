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
    ; nested ors
    '[[(x a b c) (f a (or (g b) (h c)))]] '(((x a b c) (g b ret20019) (f a ret20019)) ((x a b c) (h c ret20019) (f a ret20019)))
    ; only the last attribute of a nested and matters (like in Clojure)
    '[[(x a b c) (f a (and (g b) (h c)))]] '(((x a b c) (g b _20223) (h c ret20216) (f a ret20216)))
    ; last argument of a nested and can even be a symbol! (you can then put a not before)
    '[[(x a b c) (f a (and (g b) (h c) (not (bad c)) c))]] ' (((x a b c) (g b _20710) (h c _20711) (not (bad c)) (eq c ret20701) (f a ret20701)))))

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
          '#{(:j :f) (:h :f) (:m :n) (:g :f) (:a :d) (:p :m) (:a :b) (:f :k) (:a :c) (:i :f) (:m :o)}))))

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

