(ns enlivez.core
  (:require [datascript.core :as d]))

; https://github.com/tonsky/datascript/wiki/Tips-&-tricks#editing-the-schema

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
    (ensure! [c k] (ump! (apply f k)) nil)
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
