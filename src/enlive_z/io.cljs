(ns enlive-z.io
  (:require [enlive-z.core :as ez]
    [datascript.core :as d]))

(defn to-ws
  "Returns tx data to transact.
   Once transacted, each time a new tuple (instanciated from vars)
   is produced by the clauses then msgf is applied to this tuple to
   format it as a message. Then this message is sent over ws.
   ws is a WebSocket instance,
   clauses a sequence of datascript clauses,
   vars a sequence of datascript vars,
   msgf a function accepting as many arguments as vars has items
   and returning a payload sendable over ws."
  [ws clauses vars msgf]
  (ez/subscription [[clauses vars]]
    (fn [delta]
      (doseq [[vals addition] delta
              :when addition]
        (.send ws (apply msgf vals))))))

(defn from-ws
  "Register a message handler on ws.
   Each received message is passed to txf which returns tx data or nil.
   When non nil, the transaction data is transacted."
  [ws txf]
  (.onMessage ws
    (fn [e]
      (some->> (txf (.-data e))
        (d/transact! @#'ez/conn)))))