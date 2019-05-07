(ns enlive-z.fake
  (:require [clojure.tools.analyzer.ast :as ast]
    [cljs.analyzer :as ana.js]
    [clojure.tools.analyzer.jvm :as ana.jvm]
    [clojure.spec.alpha :as s]
    [datascript.core :as d]
    [clojure.walk :as walk]))

;; Datasource is only accessible through subscription

(def ^:private conn
  (doto (d/create-conn {::child {:db/valueType :db.type/ref
                                 :db/isComponent true
                                 :db/cardinality :db.cardinality/many}})
    (d/listen! ::meta-subscriber
      (fn [{:keys [tx-data db-after]}]
        (doseq [[eid q f] (d/q '[:find ?eid ?q ?f :where [?eid ::live-query ?q] [?eid ::handler ?f]] db-after)]
          (f (d/q q db-after)))))))

(defn subscription
  "Returns transaction.
   Upon successful transaction, the "
  "Subscription is immediate: upon subscription f receives a (positive only) delta representing the current state."
  [q f]
  [{::live-query q
    ::handler
    (let [prev-rows (atom #{})]
      (fn [rows]
        (let [prev-rows @prev-rows
              added (reduce disj rows prev-rows)
              retracted (reduce disj prev-rows rows)
              delta (-> #{}
               (into (map #(conj % true)) added)
               (into (map #(conj % false)) retracted))]
          (when (not= #{} delta)
            (f delta)))
        (reset! prev-rows rows)))}])

;; query maps

(defn attrs-keyword? [x]
  (and (keyword? x) (= "attrs" (name x))))

(def map-kvs
  (s/conformer
    #(if (map? %) (seq %) ::s/invalid)
    #(into {} %)))

(s/def ::query-map
  (s/and map-kvs
    (s/*
      (s/or :attr (s/tuple keyword? (s/or :qmap ::query-map :other (complement coll?)))
        :attrs (s/tuple (s/coll-of (some-fn keyword? symbol?) :kind vector?) attrs-keyword?)
        :defaults (s/tuple (s/map-of simple-symbol? any?) #{:or})))))

(defn- reverse-lookup
  "Returns the direct keyword when the input keyord is reversed, else returns nil."
  [k]
  (when-some [[_ n] (when (keyword? k) (re-matches #"_(.*)" (name k)))]
    (keyword (namespace k) n)))

(defn expand-query-map
  ; leveraging the spec is much work but it means the spec and this code
  ; may more easily drift away.
  [qmap]
  (let [defaults (into {} (keep (fn [[k v]] (case v :or k nil))) qmap)
        ; expand :attrs and remove :or
        qmap (into {}
               (mapcat
                 (fn [[k v]]
                   (cond
                     (= :or v) nil
                     (and (keyword? v) (= "attrs" (name v)))
                     (for [x k]
                       [(keyword (or (namespace v) (namespace x)) (name x)) (symbol (name x))])
                     :else [[k v]])))
               qmap)
        eid (:db/id qmap (gensym '?id))
        qmap (dissoc qmap :db/id)]
    {:eid eid
     :clauses (for [[k v] qmap]
                ; PONDER: outputting recursive clauses after all non-rec
                (if (map? v) ; recursive expansion
                  (let [{:keys [clauses], attr-eid :eid} (expand-query-map v)]
                    (cons
                      (if-some [k (reverse-lookup k)]
                        [attr-eid k eid]
                        [eid k attr-eid])
                      clauses))
                  (if-some [k (reverse-lookup k)]
                      [v k eid]
                      (if-some [[_ default] (find defaults k)]
                        [(list 'get-else eid k default) v]
                        [eid k v]))))}))

(defn expand-query [x]
  (let [x (if (map? x) [x] x)]
    (into [] (mapcat (fn [x] (if (map? x) (:clauses (expand-query-map x)) [x])) x))))

(defn implicit-vars [expanded-q]
  (into #{}
    (filter #(and (symbol? %) (not= '_ %) (not (.startsWith (name %) "?"))))
    ; assumes there are no extra datasources, and that a var can't appear in function
    ; position
    (tree-seq coll? (fn [x] (cond-> (seq x) (seq? x) next)) expanded-q)))

(defn datascript-q
  "Returns [binding-vector query]."
  [q]
  (let [q (expand-query q)
        vars (implicit-vars q)
        renames (zipmap vars (map #(gensym (str "?" (name %))) vars))
        where (walk/postwalk-replace renames q)]
    [(vec vars)
     (-> [:find]
       (into (map renames) vars)
       (conj :where)
       (into where))]))

(defn datascript-rule
  "Returns [binding-vector rule]."
  ([rule-name q] (datascript-rule rule-name q {}))
  ([rule-name q env]
    (let [q (expand-query q)
          vars (implicit-vars q)
          ground-vars (filter env vars)
          free-vars (remove env vars) 
          renames (zipmap vars (map #(gensym (str "?" (name %))) vars))
          where (walk/postwalk-replace renames q)
          rule-vars (into (if (seq ground-vars) [(into [] (map renames) ground-vars)] [])
                      (map renames) free-vars)
          vars (-> [] (into ground-vars) (into free-vars))]
      [(vec vars) (into [(list rule-name rule-vars)] where)])))

;; hiccup-style template

(defn walk-template [form f]
  (cond
    (vector? form) (into [] (map #(walk-template % f)) form)
    (map? form) (into {} (map (fn [[k v]] [k (walk-template v f)])) form)
    (or (symbol? form) (seq? form)) (f form)
    :else form))

(defn lift-templates
  "Replace inline templates by mount points."
  [body]
  (let [children (atom {})
        body (into []
               (map #(walk-template %
                       (fn [expr]
                         (let [mount-id (keyword (gensym 'mount))]
                           (swap! children assoc mount-id expr)
                           `(mount ~mount-id)))))
               
               body)]
    {:children @children
     :body body}))

(defn used-vars
  "vars must be a predicate"
  [expr vars]
  ; TODO amke it right: it's an overestimate
  (set (filter vars (flatten expr))))

(defn hollow* [children-templates body]
  (let [state (atom (initial-render))]
    (fn [drow])))

(defn with* [row-template]
  (let [children (atom {})]
    (fn [drow]
      (let [added (peek drow)
            row (pop drow)]
        (if added
          (swap! children assoc row (row-template row))
          (swap! children dissoc row))))))

(s/def ::deftemplate-args
  (s/cat :name symbol?
    :doc (s/? string?)
    ; options before/after params rule while making sense is not natural because init and schema
    #_#_:template-options (s/* (s/cat :option #{:css :script} :value any?))
    :params (s/coll-of (s/or :sym symbol? :qmap ::query-map)) ; PONDER allow destructuring?
    ; PONDER  if params are made of a query map then it implies taht the query may return
    ; 0, 1 or more assignments
    ; too many assignments may be dealt with with cardinality analysis
    ; none can't; best to emit a warning on no assignment?
    :options (s/* (s/cat :option #{:init :state :css :script :schema} :value any?))
    :body (s/+ any?)))

;; a component is identified by its arguments (which are stable throughout its lifecycle)
;; (different arguments would mean a resinstantiation
;; and its mountpoint (as an identical component may occur elsewhere).

;; Thus an invocation of the template is an instantiation

(defn add [{:as component :keys [n instantiate]} row]
  (if (seq row)
    (let [k (subvec row 0 n)]
      (update-in component [:children k]
        (fn [child]
          (add (or child (instantiate k) (subvec row n))))))
    component))

(defn retract [{:as component :keys [n]} row]
  (let [k (subvec row 0 n)
        remk (subvec row n)]
    (if (seq remk)
      (update-in component [:children k]
        (fn [child]
          (add (or child (instantiate k) remk))))
      (dissoc-in component [:children k]))))

`(with q )


(fn [k]
  {::live-query q
   ::handler })

(fn
  ([db k args]
    (s/subscribe db k q
      (fn [drows]
        ))))

(defmacro deftemplate [& body]
  (let [{:keys [name doc params options body]} (s/conform ::deftemplate-args body)]
    `(fn [ddb# ~args])
    ))


