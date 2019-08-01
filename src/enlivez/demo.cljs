(ns enlivez.demo
  (:require [enlivez.core :as ez]
            [datascript.core :as d]))

(ez/defhandler handler-firing-multiple-times [done]
 {:db/id item
  [title done] :item/attrs}
 (.log js/console (pr-str "hello" item title done))
 nil)

(ez/deftemplate new-item []
  :state {:db/id self
          new-todo ""}
  [:h1 {:on-click (handler-firing-multiple-times true)} "CLICK"]
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
          value ""}
  "X"
  [:input {:value value :on-change [[:db/add self ::value (-> % .-target .-value)]]}])

#_(ez/deftemplate todo []
   :state {:db/id self
           a 69}
   [:div "so far so good"
    [:span {:on-click [[:db/add self ::a (inc a)]]} "A is " a]
    [:div (an-input)]
    [:div
     [:button {:on-click [{:foo/bar (.now js/Date)}]} "Add"]
     (ez/for [{[bar] :foo/attrs}]
       :state {:db/id state
               :count 0
               foo bar}
       [:div "created at " bar]
       "but " foo
       (an-input)
       [:button 
        {:on-click [[:db/add state ::foo (inc foo)]]}
        "Bump"])]])

(defn show []
  (let [conn @#'ez/conn] ; don't try this at home!
    (d/reset-conn! conn (d/empty-db (:schema @conn)))
    (ez/mount todo (.-body js/document))
    (:tx-data (d/transact! conn [{:item/title "something" :item/done false}
                                 {:item/title "something else" :item/done false}]))))


(comment
  (datascript.core/q
    '[:find ?self39344 ?self39325 ?value39327
      :where [(vector) ?sk64] [?self39344 :enlivez.core/key ?sk64] [(vector / 1) ?sk65] [?self39325 :enlivez.core/key ?sk65] [?self39325 :enlivez.demo/value ?value39327]]
    @enlivez.core/conn)
  
  (datascript.core/q
    '[:find ?self39344 ?self39325 ?sk65 ?value39327
      :where [(vector) ?sk64] [?self39344 :enlivez.core/key ?sk64] [(vector :/ 1) ?sk65] [?self39325 :enlivez.core/key ?sk65] [?self39325 :enlivez.demo/value ?value39327]]
    @enlivez.core/conn)
  
  (datascript.core/q
    '[:find ?k
      :where [_ :enlivez.core/key ?k]]
    @enlivez.core/conn)
  
  (defrule validation-error [input msg]
    ; defrule can also extend an existing rule: it's open, so you can contribute new validators
    ; by simply adding a defrule
    ; (maybe an extend-rule helper that checks for existence etc. could be handy to have a split between declaration
    ;  and extension -- like defmulti defmethod)
    {:input/value ""
     :db/id input
     :input/label label
     :validators :validators/non-empty}
    [(str label " can't be empty." ) msg])
  
  (defrule form-errors
    "Returns all error messages for a form"
    [form msg]
    {:db/id form
     :form/input input}
    (validation-error input msg))
  
  ; same thing in an alternate syntax
  (defrule form-errors [form msg]
    (validation-error (:form/input form) msg))
  
  ; disabling submit button:
  :disabled (ez/for (form-errors form _) true)
  
  ; listing errors under a field is an ez/for
  )



