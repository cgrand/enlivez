(ns enlivez.impl.seminaive-tests
  (:require [enlivez.impl.seminaive :as impl])
  #?(:clj
     (:use [clojure.test :only [deftest is]])
     :cljs
     (:use-macros [cljs.test :only [deftest is]]))
  (:require [datascript.core :as d]
    #_[enlivez.core :as ez]))

(def rsg-edb '{up #{[a e] [a f] [f m] [g n] [h n] [i o] [j o]}
   flat #{[g f] [m n] [m o] [p m]}
   down #{[l f] [m f] [g b] [h c] [i d] [p k]}})

(deftest rsg
  (is (= ('rsg (impl/eval-rules
                 rsg-edb
                 '[([rsg x y] [flat x y])
                   ([rsg x y] [up x x1] [rsg y1 x1] [down y1 y])]))
        '#{(j f) (h f) (m n) (g f) (a d) (p m) (a b) (f k) (a c) (i f) (m o)})))

(deftest lifting
  (is (= (set (impl/lift-all
                '[([rsg x y] (or [flat x y]
                               (and [up x x1] [rsg y1 x1] [down y1 y])))]))
        '#{([rsg x y] [flat x y])
           ([rsg x y] [up x x1] [rsg y1 x1] [down y1 y])})))

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
                 (lift-all
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
