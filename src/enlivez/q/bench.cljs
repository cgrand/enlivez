(ns enlivez.q.bench
  (:require
    [datascript.core :as d]
    [enlivez.q :as q]))

(let [db (d/db-with (d/empty-db {:book/title {:db/index true}
                                 :book/author {:db/index true}})
           [{:book/title "Les Misérables" :book/author "Hugo" :book/lang "fr"}
            {:book/title "Moby Dick" :book/author "Melville"}
            {:book/title "Ulysses" :book/author "Joyce"}])]
  
  (simple-benchmark [db (d/db-with db
                          (for [n (range 1000)]
                            {:book/title (str "Book #" n)
                             :book/author (["Joyce" "Hugo" "Melville"] (mod n 3))}))
                     pq (q/prepare-query '[title] '[(or [book :book/author "Joyce"] [book :book/author "Hugo"])
                                                    [book :book/title title] [book :book/title "Ulysses"]])]
    (pq db)
    100)
  
  (simple-benchmark [db (d/db-with db
                          (for [n (range 1000)]
                            {:book/title (str "Book #" n)
                             :book/author (["Joyce" "Hugo" "Melville"] (mod n 3))}))
                     pq (q/prepare-query '[title] '[(or [book :book/author "Joyce"] [book :book/author "Hugo"])
                                                    [book :book/title title] (= title "Ulysses")])]
    (pq db)
    100)
  
  (simple-benchmark [db (d/db-with db
                          (for [n (range 1000)]
                            {:book/title (str "Book #" n)
                             :book/author (["Joyce" "Hugo" "Melville"] (mod n 3))}))
                     pq (q/prepare-query '[title] '[(or [book :book/author "Joyce"] [book :book/author "Hugo"])
                                                    [book :book/title title] (not (= title "Ulysses"))])]
    (pq db)
    100)
  
  (simple-benchmark [db (d/db-with db
                          (for [n (range 1000)]
                            {:book/title (str "Book #" n)
                             :book/author (["Joyce" "Hugo" "Melville"] (mod n 3))}))]
    (d/q '[:find ?title :where (or [?book :book/author "Joyce"] [?book :book/author "Hugo"])
           [?book :book/title ?title] [?book :book/title "Ulysses"]]
      db)
    100)
  
  (simple-benchmark [db (d/db-with db
                          (for [n (range 1000)]
                            {:book/title (str "Book #" n)
                             :book/author (["Joyce" "Hugo" "Melville"] (mod n 3))}))]
    (d/q '[:find ?title :where (or [?book :book/author "Joyce"] [?book :book/author "Hugo"])
           [?book :book/title ?title] [(= ?title "Ulysses")]]
      db)
    100)
  
  (simple-benchmark [db (d/db-with db
                          (for [n (range 1000)]
                            {:book/title (str "Book #" n)
                             :book/author (["Joyce" "Hugo" "Melville"] (mod n 3))}))]
    (d/q '[:find ?title :where (or [?book :book/author "Joyce"] [?book :book/author "Hugo"])
           [?book :book/title ?title] (not [(= ?title "Ulysses")])]
      db)
    100)
  
  (simple-benchmark [db (d/db-with db
                      (for [n (range 1000)]
                        (cond-> {:book/title (str "Book #" n)}
                          (odd? n) (assoc :book/lang "en"))))
                 pq (q/prepare-query '[title lang] '[[book :book/title title]
                                 (or-else [book :book/lang lang]
                                   (= lang "n/a"))])]
    (pq db)
    100)
    
  (simple-benchmark [db (d/db-with db
                          (for [n (range 1000)]
                            (cond-> {:book/title (str "Book #" n)}
                              (odd? n) (assoc :book/lang "en"))))]
    (d/q '[:find ?title ?lang
           :where [?book :book/title ?title]
           [(get-else $ ?book :book/lang "n/a") ?lang]] db)
    100))

