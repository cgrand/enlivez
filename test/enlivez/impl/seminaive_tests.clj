(ns enlivez.impl.seminaive-tests
  (:use [enlivez.impl.seminaive]
    [clojure.test]))

(def rsg-edb '{up #{[a e] [a f] [f m] [g n] [h n] [i o] [j o]}
   flat #{[g f] [m n] [m o] [p m]}
   down #{[l f] [m f] [g b] [h c] [i d] [p k]}})

(deftest rsg
  (is (= ('rsg (eval-rules
                rsg-edb
                '[([rsg x y] [flat x y])
                  ([rsg x y] [up x x1] [rsg y1 x1] [down y1 y])]))
        '#{(j f) (h f) (m n) (g f) (a d) (p m) (a b) (f k) (a c) (i f) (m o)})))

(deftest lifting
  (is (= (set (lift-ors
                '[([rsg x y] (or [flat x y]
                               (and [up x x1] [rsg y1 x1] [down y1 y])))]))
        '#{([rsg x y] [flat x y])
           ([rsg x y] [up x x1] [rsg y1 x1] [down y1 y])})))

(deftest fnrel
  (let [r (rel [[1 0]])
        r (reduce #(%1 %2) r [[1 2 3] [4 5 6] [8 2 9]])]
    (is (= (set (r)) #{[1 2 3] [4 5 6] [8 2 9]}))
    (is (= (set (r #{1} [nil 2 nil])) #{[1 2 3] [8 2 9]}))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
          #"Unsupported binding profile"
          (set (r #{0} [2 nil nil]))))))