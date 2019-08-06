(ns enlivez.interop.reagent
  (:require [reagent.core :as r]
    [enlivez.core :as ez]))

(defn mount
  "Regaent class to mount an EZ template."
  ([template] (mount [:div] template))
  ([container template]
    (r/create-class
      {:component-did-mount
       (fn [comp]
         (let [node (r/dom-node comp)]
           (ez/mount template node)
           nil))
       :component-did-update
       (fn [comp]
         (.log js/console "COMP" comp))
       :reagent-render (constantly container)})))
