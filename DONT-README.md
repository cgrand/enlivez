# Enlive Z

Enlive Z (EZ for short) allows to write relational logic UIs. Yes, Datalog-powered UIs!

Don't run yet! Please have a look at this simple counter:

```clj
(require '[enlivez.core :as ez]

(ez/deftemplate app []
  :state {:db/id self
          :value 42}
  [:button
   {:on-click [[:db/add self :value (inc (:value self))]]}
   "Current value: " (:value self)])

(ez/mount #'app (.-body js/document))
```

## Rationale

Since Codd's 1970 paper "A Relational Model of Data for Large Shared Data Banks", there's no ambiguity on the superiority of the relational model.

However we suffer from a boundaries between the relational world of the database and the hierarchical/object/graph world of the application.

This boundary is materialized by queries and the amount of code devoted to building hierarchical/object/graph intermediate representations from their result sets.

Modifications impact at least 3 places:
 * where a piece of data is used,
 * where it is transformed
 * where it is sourced.
 
The first two points (building and walking the intermediate representation) are incidental complexity because the shape of the intermediate representation (IR) is determined by the shape of the code.

By writing the UI in a language that translates to relational logic we can avoid having to explicit the IR.

By writing UI in EZ we strive for expressiveness.

### Bonuses

As a bonus, it is possible to take the derivative of a relational logic program. Thus, long term, it will be possible to only ever compute deltas and directly updates the DOM instead of querying, computing a whole IR, rendering it, diffing a virtual DOM, updating the actual DOM.

Please note that the current state of affairs is already a bit more parsimonious: query, diff result sets, create new vdom by updating the previous one, diff vdoms (which is more efficient because they share

### Wider architecture

All IO should happen as a consequence of updating the DB.

## Datalog gets expressive

The theoretical roots of Datalog makes it verbose in practice.

EZ offers an expression-based syntax that internally expands to "regular" Datalog. It's also a departure from Datomic/Datascript-style query language.

In EZ, `(:spouse (:child me))` is equivalent to `[:find ?spouse . :in $ ?me :where [?me :child ?c] [?c :spouse ?spouse]`.

This works because EZ makes the distinction on whether a form appears in *statement* or in *expression* context.

```
statement = ('not' statement+) | (pred top-expr+)
top-expr = (pred expr+) | literal | var
expr = top-expr | '%'
```

When a form is in expression position (that is it appears nested in arguments position of another one) it gets unnested by appending an extra variable to it and replacing itsef by this very same variable in the parent form. Thus `(:spouse (:child me))` first becomes `(:spouse (:child me) spouse#)` because the whole thing is assumed to be in expression context; then `(:child me)` gets unnested: `(:child me child#) (:spouse child# spouse#)`.

The order of arguments to keywords may look unfamiliar in statement context: `(:attr entity value)` or `(:attr entity default value)`  but it's there to enable the nice clojuresque expression syntax. 

## Why this Z ?

Z because a Z is a sideways N. Enlive Z achieves the goals that were set for the failed Enlive N.

Because "Enlive" contains the ELVN letters and [Eleven](http://runeleven.com) sponsors EZ development.

Z like [Zeno](https://skillsmatter.com/skillscasts/12820-keynote-zeno-and-the-tar-pit).

Z to pay homage to Mazinger Z and Dragon Ball Z. (Thus an Enlive GT or an Enlive Super are not out of question.)

Z like zombie because it's Enlive N raising from the grave (hierarchical model killed EN).

(Add your own.)

## License

Copyright © 2019 FIXME

Distributed under the Eclipse Public License either version 1.0 or (at
your option) any later version.


# HERE BE DRAGONS: OLD DOCUMENTATION

## Handlers

Handlers in EZ templates are not functions but expressions. These expressions must evaluate to transaction data.

There are two implicit locals available to handler expressions: `%` for the event and `%this` for the Javascript `this`.

Since handlers expression are, well, expressions you can use any function or macro inside them.

## Queries
A query is either a map, a list or a vector.

A list is a query operation, whose head is amongst `=`, `not=`, `and`, `or` or `not` (and the more experimental `if` and `or-else`).

A vector is either a pattern `[e a v]` or a function call `[(f arg1 .. argN) ret]` (See `enlivez.q/builtins` and `enlivez.q/register-fn` to know or extend available fns.)

However there's an irregularity: at the root of a query, a vector has to be interpreted as a shortand for `and`.

### Query Maps
Many queries can be expressed by using the query-map syntax. This syntax can be seen as a mix
of pattern matching, and destructuring with a pinch of pull syntax.

The core of the syntax is made of only two concepts: pattern matching and defaults. Everything else are shorthands that can be expressed with the core syntax.

#### Pattern matching
Map entries whose keys are keywords (`:db/id` or attributes -- regular or reversed) are pattern entries and their values may be either values, unqualified symbols (or `_`) or maps.

`{:person/birth-year 1978}` matches entities whose `:person/birth-year` attribute is valued to 1978; it's equivalent to `[[_ :person/birth-year 1978]]` in Datomic query language.

`{:person/name name }` retrieves names of entities whose birth year is 1978; it's equivalent to `[:find ?name :where [[?p :person/birth-year 1978] [?p :person/name ?name]]]` in Datomic query language.

`{:person/name name :person/children {:person/name "John"}}` returns names of persons who have one kid named John. `[:find ?name :where [[?p :person/children ?c] [?c :person/name "John"] [?p :person/name ?name]]]`.

The same query could have been expressed as `{:person/name "John" :person/_children {:person/name name}}`.

If a symbol (except `_` of course) is bound twice it must be bound to the same value: `{:person/name name :person/children {:person/name name}}` finds name of person who gave the same name to their kid.

#### Defaults
Map entries whose _values_ are `:or` have defaults maps as keys.

```clj
{:person/middle-name mname
 {mname "-"} :or}
```

#### Shorthands
