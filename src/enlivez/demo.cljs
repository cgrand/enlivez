(ns enlivez.demo
  (:require [enlivez.core :as ez]
            [datascript.core :as d]))

(let [conn @#'ez/conn] ; don't try this at home!
  (d/reset-conn! conn
    (d/empty-db (into (:schema @conn)
                  {:todo/items {:db/valueType :db.type/ref
                                :db/cardinality :db.cardinality/many}}))))

; when something can't be easily expressed in logic,
; it's always possible to call a clojure function
(defn toggle-order [order]
  (case order
    :ascending :descending
    :descending :ascending))

(defn render-order [order]
  (case order
    :ascending "ascending"
    :descending "descending"))

(ez/deftemplate items-filter [self]
  [:label
   [:input {:type :checkbox
            :checked (:show-done self)
            :on-change [[:db/add self :show-done (./not (:show-done self))]]}]
   "Show done?"]
  [:button {:on-click
            [[:db/add self :order (toggle-order (:order self))]]}
   (render-order (:order self))])

; handlers are just rules
(ez/defrule end-edition [self item] :=
  [[:db/add self :editing false]
   [:db/add item :title (:draft self)]])

(ez/deftemplate editable-item [item]
  :state {:db/id self
          :editing false}
  (ez/for [false (:editing self)]
    [:span {:on-double-click
            (and
              (.preventDefault %event)
              [{:db/id self :editing true :draft (:title item)}])} 
     (:title item)])
  (ez/for [true (:editing self)]
    [:form {:style {:display :inline}
            :on-submit
            (and
              (.preventDefault %event)
              (end-edition self item))}
     [:input {:value (:draft self)
              :on-change [[:db/add self :draft (.-value (.-target %event))]]
              :on-blur (end-edition self item)}]]))

(defn sort-order [order done title]
  [done (cond-> title (= order :descending) ez/desc)])

(ez/deftemplate todo []
  :state {:db/id self
          :new-item ""
          :show-done true
          :order :ascending}
  [:div
   (items-filter self)
   [:ul
    [:li [:form {:on-submit
                 (and (.preventDefault %event)
                   [{:todo/_items self
                     :title (:new-item self)
                     :done false}
                    [:db/add self :new-item ""]])}
          [:input {:value (:new-item self)
                   :on-change
                   [[:db/add self :new-item (.-value (.-target %event))]]}]]]
    (ez/for [item (:todo/items self)
             :when (or (:show-done self true)
                     (and (:show-done self false)
                       (:done item false)))]
      :sort (sort-order (:order self) (:done item) (:title item))
      [:li [:input {:type :checkbox
                    :checked (:done item)
                    :on-change
                    [[:db/add item :done (./not (:done item))]]}]
       (editable-item item)])]])

(ez/mount #'todo (.-body js/document))

; a trigger is notified when a match comes in existence
; but also when it vanishes
(ez/deftrigger console-log [true (:done item)
                            t (:title item)]
  :start
  (.log js/console "new done item" t)
  :stop
  (.log js/console "item undone" t))

