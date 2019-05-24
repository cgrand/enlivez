(ns enlive-z.demo
  (:require [enlive-z.core :as ez]
    [datascript.core :as d]))

(ez/deftemplate todo []
  :init {::new-todo ""}
  :state {:db/id self
          [new-todo] ::attrs}
  [:ul
   [:li
    [:input {:value new-todo
             :on-change [[:db/add self ::new-todo (-> % .-target .-value)]]}]
    [:button {:disabled (= "" new-todo)
              :on-click [{:item/title new-todo :item/done false}
                          ]}]]
   (ez/for {:db/id item [title done] :item/attrs}
     :state {:db/id self2
             [editing working-title] ::attrs
             {editing false
              working-title ""} :or}
     [:li
      [:input {:type :checkbox :checked done
               :on-change [[:db/add item :item/done (not done)]]}]
      [:span {:on-click (when (not editing) [{:db/id self2 ::editing true ::working-title title}])} 
       (ez/for [[(= editing false)]] title)
       (ez/for [[(= editing true)]]
         [:input {:value working-title
                  :on-change [[:db/add self2 ::working-title (-> % .-target .-value)]]
                  :on-blur [[:db/add self2 ::editing false]
                            [:db/add item :item/title working-title]]}])]])])

(defn show []
  (d/reset-conn! ez/conn (d/empty-db {:enlive-z.core/child {:db/valueType :db.type/ref
                                                            :db/isComponent true
                                                            :db/cardinality :db.cardinality/many}
                                      :enlive-z.core/key {:db/unique :db.unique/identity}}))
  (ez/mount todo (.-body js/document))
  (:tx-data (d/transact! ez/conn [{:item/title "something" :item/done false}
                                  {:item/title "something else" :item/done false}])))
