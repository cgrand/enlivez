(ns enlive-z.core
  (:require-macros enlive-z.core)
  (:require [datascript.core :as d]))

; https://github.com/tonsky/datascript/wiki/Tips-&-tricks#editing-the-schema

;; Datasource is only accessible through subscription

#_(def ^:private conn
   (doto (d/create-conn {::child {:db/valueType :db.type/ref
                                  :db/isComponent true
                                  :db/cardinality :db.cardinality/many}})
     (d/listen! ::meta-subscriber
       (fn [{:keys [tx-data db-after]}]
         (doseq [[eid q f] (d/q '[:find ?eid ?q ?f :where [?eid ::live-query ?q] [?eid ::handler ?f]] db-after)]
           (f (d/q q db-after)))))))


(defprotocol Component
  (ensure! [c k] "Returns the child component")
  (delete! [c k] "Deletes the child component"))

(defn ensure-path! [component path]
  (reduce ensure! component path))

(defn delete-path! [component path]
  (-> (reduce ensure! component (pop path))
    (delete! (peek path))))

(defn with-component [child ump!]
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

(defn with-template [q ks vars child]
  (let [[qks child] child
        qks (map #(cons [q ks] %) (cons nil qks))]
    [qks #(with-component child %)]))

(defn fragment-template [body children]
  (let [qks (for [[i [path [qks]]] (map vector (range) children)
                  qk qks]
              (cons `[[(~'ground ~i) ?child#] [?child#]] qk))
        children (vec (for [[path [qks f]] children]
                        [path f]))]
    [qks #(fragment-component body children %)]))

(defn terminal-template [args f]
  [[[[] args]] #(terminal-component f %)])
  
(declare ^::special with ^::special fragment ^::special terminal)

#_ (ez/deftemplate todo []
    [:ul
     (ez/with {[title done] :item/attrs}
       [:li title " is " (if done "done!" "yet to do...")])])

#_ (let [[qks compo] todo
           dom (atom nil)] ; "hiccup dom" pour les tests
      (doto (compo #(reset! dom %)) ; on monte le composant
        ; send updates
        (ez/ensure-path! [[0] [12345] [0] ["World domination"]])
        (ez/ensure-path! [[0] [12345] [1] [false]])
        (ez/ensure-path! [[0] [78910] [0] ["Buy AirPods"]])
        (ez/ensure-path! [[0] [78910] [1] [true]]))
      @dom)