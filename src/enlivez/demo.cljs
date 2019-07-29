(ns enlivez.demo
  (:require [enlivez.core :as ez]
            [datascript.core :as d]))

(ez/deftemplate new-item []
  :state {:db/id self
          new-todo ""}
  [:li
   [:form {:on-submit (do
                        (.preventDefault %)
                        [{:item/title new-todo :item/done false}
                         [:db/add self ::new-todo ""]])}
    [:input {:value new-todo
             :on-change (doto [[:db/add self ::new-todo (-> % .-target .-value)]] prn)}]
    [:button {:disabled (= "" new-todo)} "Add!"]]])

(ez/deftemplate items-filter [self show-done]
  [:label
   [:input {:type :checkbox
            :checked show-done
            :on-click [[:db/add self ::show-done (not show-done)]]}]
   "Show done?"])

(ez/deftemplate sort-btn [self show-done]
   [:label
    [:input {:type :checkbox
             :checked show-done
             :on-click [[:db/add self ::show-done (not show-done)]]}]
    "Show done?"])

(defn on-blur [self item working-title]
  [[:db/add self ::editing false]
   [:db/add item :item/title working-title]])

(ez/deftemplate todo []
  :state {:db/id self
          show-done true
          order :ascending}
  [:ul
   (new-item)
   [:div
    (items-filter self show-done)
    [:button {:on-click [[:db/add self ::order (case order
                                                 :ascending :descending
                                                 :descending :ascending)]]}
     (case order
       :ascending "descending"
       :descending "ascending")]]
   (ez/for (not (and {:db/id item
                      [title done] :item/attrs}
                  (or (= true show-done)
                    (= false done))))
     ; when nothing to display
     (ez/for {:db/id item
              [title done] :item/attrs}
       ; but still some done items
       [:li [:i "Do you want to see "
             [:a {:href "#" :on-click (do (.preventDefault %) [[:db/add self ::show-done true]])}
              "all you've already achieved?"]]])
     (ez/for (not {:db/id item
                   [title done] :item/attrs})
       ; really nothing
       [:li [:i "Time to write down some tasks!"]]))
   (ez/for
    (and {:db/id item
          [title done] :item/attrs}
      (or (= true show-done)
        (= false done)))
    #_[[item :item/title title]
       [item :item/done done]
       (= done show-done)]
     :state {:db/id self
             editing false
             working-title ""}
     :sort (case order
             :descending [done (ez/desc title)]
             [done title])
     [:li
      [:input {:type :checkbox :checked done
               :on-change [[:db/add item :item/done (not done)]]}]
      [:span
       [:span {:on-click (when (not editing) [{:db/id self ::editing true ::working-title title}])}
        (ez/for (= editing false) title)
        (ez/for (= editing true)
         [:input {:value working-title
                  :on-change [[:db/add self ::working-title (-> % .-target .-value)]]
                  :on-blur (on-blur self item working-title)}])]
       [:button
        {:on-click (doto [[:db/retractEntity item]] prn)}
        "X"]]])])

(defn show []
  (let [conn @#'ez/conn] ; don't try this at home!
    (d/reset-conn! conn (d/empty-db (:schema @conn)))
    (ez/mount todo (.-body js/document))
    (:tx-data (d/transact! conn [{:item/title "something" :item/done false}
                                 {:item/title "something else" :item/done false}]))))






