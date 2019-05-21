(ns enlive-z.core
  (:require-macros enlive-z.core)
  (:refer-clojure :exclude [for])
  (:require
    [clojure.core :as clj]
    [datascript.core :as d]
    [reagent.core :as r]))

; https://github.com/tonsky/datascript/wiki/Tips-&-tricks#editing-the-schema

;; Datasource is only accessible through subscription
(def conn
  (doto (d/create-conn {#_#_::child {:db/valueType :db.type/ref
                                     :db/isComponent true
                                     :db/cardinality :db.cardinality/many}})
    (d/listen! ::meta-subscriber
      (fn [{:keys [tx-data db-after]}]
        (doseq [[eid q f] (d/q '[:find ?eid ?q ?f :where [?eid ::live-query ?q] [?eid ::handler ?f]] db-after)]
          (f (d/q q db-after)))))))

(defn txing-handler [f]
  (fn [e]
    (.preventDefault e) ; TODO: make it possible to opt out
    (this-as this
      (when-some [tx (.call f this e)]
        (d/transact! conn (if (map? tx) [tx] tx))))))

(defprotocol Component
  (ensure! [c k] "Returns the child component")
  (delete! [c k] "Deletes the child component"))

(defn ensure-path! [component path]
  (reduce ensure! component path))

(defn delete-path! [component path]
  (-> (reduce ensure! component (pop path))
    (delete! (peek path))))

(defn for-component [child ump!]
  (let [children (atom {})
        ordered-ks (atom [])
        doms (atom {})]
    (reify Component
      (ensure! [c k]
        (or (@children k)
          (let [child (child
                        #(let [doms (swap! doms assoc k %)]
                           (ump! (map doms @ordered-ks))))]
            (swap! ordered-ks conj k)
            (swap! children assoc k child)
            child)))
      (delete! [c k]
        (swap! ordered-ks #(vec (remove #{k} %)))
        (swap! children dissoc k)
        (swap! doms dissoc k)
        nil))))

(defn fragment-component [dom children ump!]
  (let [adom (atom dom)
        children
        (into []
          (map (fn [[path child]]
                 (child #(ump! (swap! adom assoc-in path %)))))
          children)]
    (ump! dom)
    (reify Component
      (ensure! [c [i]] (nth children i))
      (delete! [c k] nil))))

(defn terminal-component [f ump!]
  (reify Component
    (ensure! [c k] (ump! (f k)) nil)
    (delete! [c k] nil)))

(defn for-template [q ks child]
  (let [[qks child] child
        qks (map #(cons [q ks] %) (cons [[[] []]] qks))] ; [[] []] is to help detect upserts
    [qks #(for-component child %)]))

(defn fragment-template [body children]
  (let [?child (gensym '?child)
        qks (clj/for [[i [path [qks]]] (map vector (range) children)
                  qk qks]
              (cons `[[[(~'ground ~i) ~?child]] [~?child]] qk))
        children (vec (clj/for [[path [qks f]] children]
                        [path f]))]
    [qks #(fragment-component body children %)]))

(defn terminal-template [args f]
  [[[[[] args]]] #(terminal-component f %)])
  
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
  (let [where (mapcat first hq)
        find (mapcat second hq)
        seg-fns (mapv (fn [[from to]]
                        #(subvec % from to))
                  (partition 2 1 
                    (reductions + 0 (map (fn [[_ k]] (count k)) hq))))]
    [`[:find ~@find :where ~@where]
     (fn [row] (into [] (map #(% row)) seg-fns))]))

(defn- subscription
  "Returns transaction.
   Upon subscription f receives a (positive only) delta representing the current state."
  [hq f]
  (let [[q path-fn] (flatten-q hq)]
    (prn q)
    [{::live-query q
      ::handler
      (let [aprev-paths (atom {})]
        (fn [rows]
          (prn 'ROWS rows)
          (let [prev-paths @aprev-paths
                ; I could also use a flat sorted map with the right order
                paths (into {} (comp (map path-fn) (map (fn [path] [(pop path) path]))) rows)
                _ (prn 'PS paths)
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
              (prn 'DELTA delta)
              (f delta)))))}]))

(defn mount [template elt]
  (let [dom (r/atom nil)
        [qks instantiate!] template
        component (instantiate! #(reset! dom %))
        update! (fn [delta]
                  (doseq [path delta
                          :let [upsert (peek path)
                                path (pop path)
                                f (if upsert ensure-path! delete-path!)]]
                    (f component path)))
        subscriptions (mapcat #(subscription % update!) qks)]
    (d/transact! conn subscriptions)
    (r/render [#(first (simplify @dom))] elt)))

(comment
  (require '[enlive-z.core :as ez] '[datascript.core :as d])
  (d/reset-conn! ez/conn (d/empty-db {}))
  (ez/deftemplate todo []
    [:ul
     #_[:li [:form
             {:on-submit {:item/title "new item" :item/done false}}
             [:input {:type :text}] [:button {:type :submit}]]]
     (ez/for {:db/id item [title done] :item/attrs}
      [:li 
       {:on-click [[:db/add item :item/done (not done)]]}
       title " is " (if done "done!" "yet to do...")])])
   (ez/mount todo (.-body js/document))
   (:tx-data (d/transact! ez/conn [{:item/title "something" :item/done false}
                                   {:item/title "something else" :item/done false}]))
   
 )


#_ (let [[qks compo] todo
           dom (atom nil)] ; "hiccup dom" pour les tests
      (doto (compo #(reset! dom %)) ; on monte le composant
        ; send updates
        (ez/ensure-path! [[0] [12345] [0] ["World domination"]])
        (ez/ensure-path! [[0] [12345] [1] [false]])
        (ez/ensure-path! [[0] [78910] [0] ["Buy AirPods"]])
        (ez/ensure-path! [[0] [78910] [1] [true]]))
      (r/render (ez/simplify @dom) app))