(ns enlive-z.core
  (:require-macros enlive-z.core)
  (:refer-clojure :exclude [for])
  (:require
    [clojure.core :as clj]
    [datascript.core :as d]
    [reagent.core :as r]))

; https://github.com/tonsky/datascript/wiki/Tips-&-tricks#editing-the-schema

;; Datasource is only accessible through subscription
(def ^:private ^:dynamic *reentrant* false)

(def conn
  (doto (d/create-conn {::child {:db/valueType :db.type/ref
                                 :db/isComponent true
                                 :db/cardinality :db.cardinality/many}
                        ::key {:db/unique :db.unique/identity}})
    (d/listen! ::meta-subscriber
      (fn [{:keys [tx-data db-after]}]
        (when-not *reentrant*
          (binding [*reentrant* true]
           (doseq [[eid q f] (d/q '[:find ?eid ?q ?f :where [?eid ::live-query ?q] [?eid ::handler ?f]] db-after)]
             (f (d/q q db-after)))))))))

(defn txing-handler [f]
  (fn [e]
    #_(.preventDefault e) ; TODO: make it possible to opt out
    #_(.stopPropagation e) ; TODO: make it possible to opt out
    (this-as this
      (when-some [tx (.call f this e)]
        (d/transact! conn (if (map? tx) [tx] tx))))))

(defprotocol Component
  (ensure! [c ks] "Returns the child component for (peek ks)")
  (delete! [c k] "Deletes the child component"))

(defn ensure-path! [component path]
  (reduce ensure! component (next (reductions conj [] path))))

(defn delete-path! [component path]
  (some-> (reduce get component (pop path))
    (delete! (peek path))))

(defn for-component [child ump! parent-state-eid flat-ks]
  (let [children (atom {})
        ordered-ks (atom [])
        doms (atom {})]
    (reify 
      ILookup
      (-lookup [c k] (@children k))
      Component
      (ensure! [c ks]
        (let [k (peek ks)]
          (or (@children k)
            (let [child (child
                          #(let [doms (swap! doms assoc k %)]
                             (ump! (map doms @ordered-ks)))
                          parent-state-eid (into flat-ks k))]
              (swap! ordered-ks conj k)
              (swap! children assoc k child)
              child))))
      (delete! [c k]
        (swap! ordered-ks #(vec (remove #{k} %)))
        (swap! children dissoc k)
        (swap! doms dissoc k)
        (ump! (map doms @ordered-ks))
        nil))))

(defn fragment-component [dom children ump! parent-state-eid flat-ks]
  (let [adom (atom dom)
        children
        (into []
          (map-indexed
            (fn [i [path child]]
              (child #(ump! (swap! adom assoc-in path %)) parent-state-eid
                (conj flat-ks i))))
          children)]
    (ump! dom)
    (reify
      ILookup
      (-lookup [c k]
        (let [[i] k]
          (if (some? i)
            (nth children i)
            c)))
      Component
      (ensure! [c ks] (get c (peek ks)))
      (delete! [c k] nil))))

(defn terminal-component [f ump! parent-state-eid flat-ks]
  (reify
    ILookup
    (-lookup [c k] nil)
    Component
    (ensure! [c ks] (ump! (f (peek ks))) nil)
    (delete! [c k] nil)))

(defn state-component [entity-map child ump! parent-state-eid flat-ks]
  (prn 'CREATING 'STATE)
  (let [entity-map (assoc entity-map :db/id -1 ::key (apply pr-str flat-ks)) ; added apply pr-str because https://github.com/tonsky/datascript/issues/262
        {state-eid -1} (:tempids (d/transact! conn [entity-map [:db/add parent-state-eid ::child -1]]))
        child (child ump! state-eid flat-ks)]
    (reify
      ILookup
      (-lookup [c k] (-lookup child k))
      Component
      (ensure! [c ks] (ensure! child ks))
      (delete! [c k]
        (try
          (delete! child k)
          (finally
            (d/transact! conn [[:db/retract parent-state-eid ::child state-eid]
                               [:db/retractEntity state-eid]]))) ))))

(defn for-template [q ks child]
  (let [[qks child] child
        qks (map #(cons [q ks] %) (cons [[[] []]] qks))] ; [[] []] is to help detect upserts
    [qks #(for-component child %1 %2 %3)]))

(defn fragment-template [body children]
  (let [qks (clj/for [[i [path [qks]]] (map vector (range) children)
                  qk qks]
              (cons [[] i] qk))
        children (vec (clj/for [[path [qks f]] children]
                        [path f]))]
    [qks #(fragment-component body children %1 %2 %3)]))

(defn terminal-template [args f]
  [[[[[] args]]] #(terminal-component f %1 %2 %3)])

(defn state-template [entity-map entity-q child]
  (let [[qks child] child]
    [(map #(cons [entity-q []] %) qks) #(state-component entity-map child %1 %2 %3)]))

(declare ^::special for ^::special fragment ^::special terminal)

(defn simplify [x]
  (if (sequential? x)
    (if (keyword? (first x))
      [(into [(first x)] (mapcat simplify (rest x)))]
      (mapcat simplify x))
    [x]))

(defn- flatten-q
  "Flattens a hierarchical query to a pair [actual-query f] where f
   is a function to map a row to a path."
  [hq]
  (prn 'HQ hq)
  (let [[where find ks seg-fns]
        (reduce
          (fn [[where find ks seg-fns] [q k]]
            (let [q (if (= `if-state (first q))
                      (let [[_ eid then else] q
                            ?sk (gensym '?sk)]
                        [[(cons 'pr-str ks) ?sk] ; was 'vector but https://github.com/tonsky/datascript/issues/262
                         (list 'or
                           (list* 'and [eid ::key ?sk] then)
                           (list* 'and (list 'not [eid ::key ?sk])
                             [(list 'list ::key ?sk) eid] else))]) ; was 'vector but https://github.com/tonsky/datascript/issues/262
                      q)
                  seg-fn (if (number? k)
                           (constantly [k])
                           (let [from (count find)
                                 to (+ from (count k))]
                             #(into [] (subvec % from to))))] ; https://clojure.atlassian.net/browse/CLJS-3092
              [(into where q)
               (into find (if (number? k) nil k))
               (into ks (if (number? k) [k] k))
               (conj seg-fns seg-fn)]))
          [[] [] [] []] hq)]
    [`[:find ~@find :where ~@where]
     (fn [row] (into [] (map #(% row)) seg-fns))]))

(defn- subscription
  "Returns transaction.
   Upon subscription f receives a (positive only) delta representing the current state."
  [hq f]
  (let [[q path-fn] (flatten-q hq)]
    [{::live-query q
      ::handler
      (let [aprev-paths (atom {})]
        (fn [rows]
          (let [prev-paths @aprev-paths
                ; I could also use a flat sorted map with the right order
                paths (into {} (comp (map path-fn) (map (fn [path] [(pop path) path]))) rows)
                deletions (reduce dissoc prev-paths (keys paths))
                upserts  (into {}
                           (remove (fn [[ks path]] (= path (prev-paths ks))))
                           paths)
                delta (-> #{}
                        (into (map #(conj % false)) (keys deletions))
                        (into
                          (comp
                            (map #(if (= [] (peek %)) (pop %) %))
                            (map #(conj % true)))
                          (vals upserts)))]
            (reset! aprev-paths paths)
            (when (not= #{} delta)
              (prn 'Q q)
              (prn 'DELTA delta)
              (f delta)))))}]))

(defn mount [template elt]
  (let [dom (r/atom nil)
        [qks instantiate!] template
        {root-eid -1} (:tempids (d/transact! conn [[:db/add -1 ::root true]]))
        component (instantiate! #(reset! dom %) root-eid [])
        update! (fn [delta]
                  (doseq [path delta
                          :let [upsert (peek path)
                                path (pop path)
                                f (if upsert ensure-path! delete-path!)]]
                    (f component path)))
        subscriptions (vec (mapcat #(subscription % update!) qks))]
    (d/transact! conn subscriptions)
    (r/render [#(first (simplify @dom))] elt)))

(comment
  (require '[enlive-z.core :as ez] '[datascript.core :as d])
  (d/reset-conn! ez/conn (d/empty-db {:enlive-z.core/child {:db/valueType :db.type/ref
                                                            :db/isComponent true
                                                            :db/cardinality :db.cardinality/many}
                                      :enlive-z.core/key {:db/unique :db.unique/identity}}))
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
                           [:db/add self ::new-todo ""]]}]]
     (ez/for {:db/id item [title done] :item/attrs}
       :state {:db/id self2
               [editing] ::attrs
               {editing false} :or}
       [:li (str item) "/" (pr-str self2)
        [:input {:type :checkbox :checked done
                 :on-change [[:db/add item :item/done (not done)]]}]
        [:span {:on-click (doto [[:db/add self2 ::editing (not editing)]] (->> (prn 'CLICK)))} 
         title
         (ez/for {:falsy editing} title)
         #_(ez/for [[(= editing false)]] title)
         #_(ez/for [[(= editing true)]] "toto")]])])
   (ez/mount todo (.-body js/document))
   (:tx-data (d/transact! ez/conn [{:falsy false}
                                   {:truthy true}
                                   {:item/title "something" :item/done false}
                                   {:item/title "something else" :item/done false}]))
   
   )
