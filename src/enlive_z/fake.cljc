(ns enlive-z.fake
  (:require [clojure.tools.analyzer.ast :as ast]
    [cljs.analyzer :as ana.js]
    [clojure.tools.analyzer.jvm :as ana.jvm]
    [clojure.spec.alpha :as s]
    [datascript.core :as d]
    [clojure.walk :as walk]
    [clojure.string :as str]))

;; Datasource is only accessible through subscription

(def ^:private conn
  (doto (d/create-conn {::child {:db/valueType :db.type/ref
                                 :db/isComponent true
                                 :db/cardinality :db.cardinality/many}})
    (d/listen! ::meta-subscriber
      (fn [{:keys [tx-data db-after]}]
        (doseq [[eid q f] (d/q '[:find ?eid ?q ?f :where [?eid ::live-query ?q] [?eid ::handler ?f]] db-after)]
          (f (d/q q db-after)))))))

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
  "Returns [binding-vector rule].
   env is a predicate returning true on upstream vars."
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

;; computing keyvars
(defn- dnf "Returns a disjunctive normal form of the clause" [clause]
  (cond
    (vector? clause) [[clause]]
    ; expression-clause
    (seq? clause)
    (case (first clause)
      and (if-some [[clause & clauses] (next clause)]
            (for [a (dnf clause) b (dnf (cons 'and clauses))]
              (concat a b))
            [[]])
      or (mapcat dnf (next clause))
      not (->> (dnf (cons 'and (next clause)))
            (reduce
              (fn [not-dnf conjunction]
                (for [clause conjunction
                      conjunction' not-dnf]
                  (conj conjunction' (list 'not clause))))
              [[]])))
    :else (throw (ex-info (str "Unexpected clause " (pr-str clause)) {:clause clause}))))

(defn- scc
  "Returns the strongly connected components of a graph specified by its nodes
   and a successor function succs from node to nodes.
   The used algorithm is Tarjan's one."
  [nodes succs]
  (letfn [(sc [env node]
            ; env is a map from nodes to stack length or nil,
            ; nil means the node is known to belong to another SCC
            ; there are two special keys: ::stack for the current stack 
            ; and ::sccs for the current set of SCCs
            (if (contains? env node)
              env
              (let [stack (::stack env)
                    n (count stack)
                    env (assoc env node n ::stack (conj stack node))
                    env (reduce (fn [env succ]
                                  (let [env (sc env succ)]
                                    (assoc env node (min (or (env succ) n) (env node)))))
                          env (succs node))]
                (if (= n (env node)) ; no link below us in the stack, call it a SCC
                  (let [nodes (::stack env)
                        scc (set (take (- (count nodes) n) nodes))
                        ; clear all stack lengths for these nodes since this SCC is done
                        env (reduce #(assoc %1 %2 nil) env scc)]
                    (assoc env ::stack stack ::sccs (conj (::sccs env) scc)))
                  env))))]
    (::sccs (reduce sc {::stack () ::sccs #{}} nodes))))

; for a conjunction (of a DNF) we emit a graph of deps
(defn- deps [conjunction schema]
  (transduce (mapcat
              (fn self [clause]
                (if (seq? clause) 
                  (case (first clause)
                    ; emit nothing on not: imagine (not [?a :ident/attr :k])
                    not nil)
                  ; else must be a vector
                  (let [[e a v] (into clause '[_ _ _])]
                    (when-not (or (= '_ e) (symbol? a) (= '_ v))
                      (cond
                        (symbol? e)
                        (cond
                          (symbol? v)
                          (when (= :db.cardinality/one (get-in schema [a :db/cardinality] :db.cardinality/one))
                            [[e v]])
                
                          (get-in schema [a :db/unique]) [[:known v]])
              
                        (seq? e)
                        (case (first e)
                          get-else (let [v a
                                         [_ src e a default] e]
                                     (recur [e a v])))
                        :else :TODO))))))
    (completing
      (fn [succs [a b]]
        (update succs a (fnil conj []) b)))
    {} conjunction))

(defn- keyset [conjunction schema known-vars]
  (let [succs (-> (deps conjunction schema)
                (update :known (fnil into []) known-vars))
        sccs (scc (keys succs) succs)
        scc-of (into {}
                 (for [scc sccs, var scc]
                   [var scc]))
        succs (into {}
                (map (fn [[a bs]]
                       (let [scc-a (scc-of a)]
                         [scc-a (into #{} (comp (remove scc-a) (map scc-of)) bs)])))
                succs)
        src-only (dissoc (reduce dissoc succs (mapcat val succs)) #{:known})]
    (keys src-only)))

(defn keyvars [expanded-q schema known-vars]
  ; in presence of many cycles the key may not be minimal
  (into #{} (comp (mapcat #(keyset % schema known-vars)) (map first)) (dnf (cons 'and expanded-q))))

;; BROKEN CODE BELOW

;; templates
;; ok se have to collect queries
;; each query should output a key segmented as a path

(defprotocol Template
  (collect-queries [t known-vars schema]
    "Returns a sequence of sequences of [keyvars other-vars expanded-q] where expanded-qs os a sequence of expanded queries
     and key-path is a sequence of [keyvars other-vars]. Both sequences MUST have the same size.")
  (emit [t]))

(defrecord With [q child]
  Template
  (collect-queries [t known-vars schema]
    (let [q (expand-query q)
          vars (implicit-vars q)
          own-keys (keyvars q schema known-vars)
          known-vars (into known-vars vars)
          segment [own-keys q]]
      (for [q (cons nil (collect-queries child known-vars schema))]
        (cons segment q))))
  (emit [t]
    `(with-component ~(emit child))))

(defn used-vars
  "vars must be a predicate"
  [expr known-vars]
  ; TODO make it right: it's an overestimate
  (set (filter known-vars (flatten expr))))

(defrecord Terminal [expr]
  Template
  (collect-queries [t known-vars schema]
    [[[(vec (used-vars expr known-vars)) []]]])
  (emit [t]
    `(terminal-component
       (fn [~@(used-vars expr known-vars)] ~expr))))

(defrecord Fragment [body children]
  Template
  (collect-queries [t known-vars schema]
    (let [child-var (gensym '?child)
          child-key [child-var]]
      (for [[i subqs]
            (map-indexed
              (fn [i t] [i (collect-queries t known-vars schema)])
              children)
            q subqs]
        (cons [child-key [[(list 'ground i) child-var]]] q))))
  (emit [t]
    `(fragment-component )))

(defn flatten-q
  "Flattens a hierarchical query to a pair [actual-query f] where f
   is a function to map a row to a path."
  [hq]
  (let [where (mapcat second hq)
        find (mapcat first hq)
        seg-fns (mapv (fn [[from to]]
                        #(subvec % from to))
                  (partition 2 1 
                    (reductions + 0 (map (fn [k] (count k)) hq))))]
    [`[:find ~@find :where ~@where]
     (fn [row] (into [] (map #(% row)) seg-fns))]))

(defn subscription
  "Returns transaction.
   Upon subscription f receives a (positive only) delta representing the current state."
  [hq f]
  (let [[q path-fn] (flatten-q hq)]
    [{::live-query q
      ::handler
      (let [prev-paths (atom {})]
        (fn [rows]
          (let [prev-paths @prev-paths
                ; I could also use a flat sorted map with the right order
                paths (into {} (comp (map path-fn) (map (fn [path] [(take-nth 2 path) path]))) rows)
                deletions (reduce dissoc prev-paths (keys paths))
                upserts  (into {}
                           (remove (fn [[ks path]] (= path (prev-paths ks))))
                           paths)
                delta (-> #{}
                        (into (map #(cons false %)) deletions)
                        (into (map #(cons true %)) (vals upserts)))]
            (when (not= #{} delta)
              (f delta)))
          (reset! prev-rows rows)))}]))

(defprotocol Component
  (ensure! [c k] "Returns the child component")
  (delete! [c k] "Deletes the child component"))

(defn fragment-component [dom children]
  (fn [ump!]
    (let [adom (atom dom)
          children
          (into []
            (map (fn [[path child]]
                   (child #(ump! (swap! adom assoc-in path %)))))
            children)]
      (ump! dom)
      (reify Component
        (ensure! [c [i]] (nth children i))))))

(defn terminal-component [f]
  (fn [ump!]
    (reify Component
      (ensure! [c k] (ump! (apply f k)) nil))))

(defn with-component [child]
  (fn [ump!]
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
              child)))))))

(defn ensure-path! [component path]
  (reduce ensure! component path))

#_(let [adom (atom nil)
       root (fragment-component [:ul :_]
              [[[1] (with-component 
                      (fragment-component [:li :_ "is" :_]
                        [[[1] (terminal-component identity)]
                         [[3] (terminal-component #(if % "done" "yet to do"))]]))]])
       root (root #(reset! adom %))]
   (doto root
     (ensure-path! [[0] [12345]])
     (ensure-path! [[0] [12345] [0] ["title"]])
     (ensure-path! [[0] [12345] [1] [false]]))
   @adom)

(defn fragment-component [up! frag children]
  (reify Component
    (ensure! [c k ump!]
      
      (ensure! (children k)  )
      (up! (f k)))))

(defrecord FragmentComponent [children]
  (ensure! [c k] (children k)))

(defrecord TerminalComponent [f]
  (ensure! [c k] (f k) c))

(defrecord WithComponent [children f]
  (ensure! [c k] (or (get children k) )))

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
  (let [children (atom [])
        body (into []
               (map #(walk-template %
                       (fn [expr]
                         (let [mount-id (dec (count (swap! children conj expr)))]
                           `(mount ~mount-id)))))
               body)]
    {:children (mapv
                 (fn [expr]
                   (if (when-some [x (when (seq? expr) (first expr))]
                         (and (symbol? x)
                           (some-> x resolve meta ::template)))
                     expr
                     `(terminal ~expr)))
                 @children)
     :body body}))







(fn [title done]
  (let [nodes ...
        title-terminal (xxx title)
        done-terminal (xxx title)]
    ))






(defmacro ^::template with
  "iteration"
  [q & body]
  ; TODO: add options (:sort)
  `{:query '~q
    :children [~(lift-templates body)]})

(defmacro ^::template terminal [expr]
  "leaf template"
  (let [vars (vec (used-vars expr &env))] 
    `{:vars ~vars
      :ffn (fn ~vars ~expr)}))


(defn- ^String camelize [k]
  (str/replace (name k) #"-(\w)" (fn [[_ l]] (.toUpperCase ^String l))))

(defn render-attrs [^StringBuilder sb attrs]
  (doseq [[k v] attrs
          :let [k (camelize k)]
          :when (and v (not (seq? v)))]
    (-> sb (.append " ") (.append k))
    (when-not (true? v)
      (-> sb (.append "=\"") (.append (str/replace (str v) "\"" "&quot;")) (.append "\""))))
  sb)

(defn render-dyn-attrs [^StringBuilder sb attrs]
  (doseq [v (vals attrs)
          :when (seq? v)]
    (-> sb (.append "<!-- ") (.append (str (second v))) (.append " -->")))
  sb)

(defn render-node [^StringBuilder sb x]
  (cond
    (vector? x)
    (let [tag (first x)
          attrs (second x)
          attrs (when (map? attrs) attrs)
          content (if attrs (nnext x) (next x))
          sb (-> sb (.append "<") (.append (name tag)) (render-attrs attrs) (.append ">"))]
      (case tag
        (:area :base :br :col :embed :hr :img :input :link :meta :param :source :track :wbr)
        nil
        (do
          (reduce render-node sb content)
          (-> sb (.append "</") (.append (name tag)) (.append ">"))))
      (render-dyn-attrs sb attrs))
    (string? x)
    (.append sb (str/replace x #"[&<]"
                  #(if (= \& (.charAt ^String % 0)) "&amp;" "&lt;")))
    ; mount
    :else (-> sb (.append "<!-- ") (.append (str (second x))) (.append " -->"))))

(defn render-fragments [xs]
  (str (reduce render-node (StringBuilder.) xs)))

`(-> js/document .createRange (.createContextualFragment ~(render-fragments)))

;; component state is 
{:children {}
 :make-instance }

(defn upsert [component path]
  (let [[[i k] & ks] (seq ks)]
    (if (component ))
    ))

{:f 
 (fn
   ([] {:h [:li nil]
        :x {[1] (fn [_ k [title _]] title)}})
   [acc [k o & path]]
   (let [[title done] o]
     [:li title ]))}






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


