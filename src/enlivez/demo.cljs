(ns enlivez.demo
  (:require [enlivez.core :as ez]
    [datascript.core :as d]))

(ez/deftemplate new-item []
  :state {:db/id self
          new-todo ""}
  [:li
    [:input {:value new-todo
             :on-change (doto [[:db/add self ::new-todo (-> % .-target .-value)]] prn)}]
    [:button {:disabled (= "" new-todo)
              :on-click [{:item/title new-todo :item/done false}
                         [:db/add self ::new-todo ""]]} "Add!"]])

(ez/deftemplate todo []
  [:ul
   (new-item)
   (ez/for {:db/id item [title done] :item/attrs}
    :state {:db/id self
            editing false
            working-title ""}
    :sort [done title]
    [:li
     [:input {:type :checkbox :checked done
              :on-change [[:db/add item :item/done (not done)]]}]
     [:span {:on-click (when (not editing) [{:db/id self ::editing true ::working-title title}])}
      (ez/for [(= editing false)] title)
      (ez/for [(= editing true)]
        [:input {:value working-title
                 :on-change [[:db/add self ::working-title (-> % .-target .-value)]]
                 :on-blur [[:db/add self ::editing false]
                           [:db/add item :item/title working-title]]}])]])])

(defn show []
  (let [conn @#'ez/conn]
    (d/reset-conn! conn (d/empty-db (:schema @conn)))
    (ez/mount todo (.-body js/document))
    (:tx-data (d/transact! conn [{:item/title "something" :item/done false}
                                 {:item/title "something else" :item/done false}]))))






