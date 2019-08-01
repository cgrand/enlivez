(ns enlivez.demo
  (:require [enlivez.core :as ez]
            [datascript.core :as d]))

#_(ez/defhandler XXX [done]
   {:db/id item
    [title done] :item/attrs}
   (.log js/console (pr-str "hello" item title done)))

#_(ez/deftemplate new-item []
   :state {:db/id self
           new-todo ""}
   [:h1 {:on-click (XXX true)} "CLICK"]
   [:li
    [:form {:on-submit (do
                         (.preventDefault %)
                         [{:item/title new-todo :item/done false}
                          [:db/add self ::new-todo ""]])}
     [:input {:value new-todo
              :on-change (doto [[:db/add self ::new-todo (-> % .-target .-value)]] prn)}]
     [:button {:disabled (= "" new-todo)} "Add!"]]])

#_(ez/deftemplate items-filter [self show-done]
   [:label
    [:input {:type :checkbox
             :checked show-done
             :on-click [[:db/add self ::show-done (not show-done)]]}]
    "Show done?"])

#_(ez/deftemplate sort-btn [self show-done]
    [:label
     [:input {:type :checkbox
              :checked show-done
              :on-click [[:db/add self ::show-done (not show-done)]]}]
     "Show done?"])

#_(defn on-blur [self item working-title]
   [[:db/add self ::editing false]
    [:db/add item :item/title working-title]])

#_(ez/deftemplate todo []
   :state {:db/id self
           show-done true
           order :ascending}
   [:div
    (ez/fragment
      :state {:db/id self}
      [:h1 "Hello state"])
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
         "X"]]])]])

(ez/deftemplate an-input []
  :state {:db/id self
          ::value ""}
  "X"
  (ez/for {:db/id self
           ::value value}
    [:input {:value value :on-change [[:db/add self ::value (-> % .-target .-value)]]}]))

(ez/deftemplate todo []
  :state {:db/id self
          :a 69}
  [:div "so far so good"
   (ez/for {:db/id self :a a} [:span {:on-click [[:db/add self :a (inc a)]]} "A is " a])
   [:div (an-input)]])

(defn show []
  (let [conn @#'ez/conn] ; don't try this at home!
    (d/reset-conn! conn (d/empty-db (:schema @conn)))
    (ez/mount todo (.-body js/document))
    (:tx-data (d/transact! conn [{:item/title "something" :item/done false}
                                 {:item/title "something else" :item/done false}]))))






