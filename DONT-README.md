# Enlive Z

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

## Why this Z ?

Z because a Z is a sideways N. Enlive Z achieves the goals that were set for the failed Enlive N.

Z like (Zeno) [lien vers Zeno et le tarpit].

Z to pay homage to Mazinger Z and Dragon Ball Z. (So an Enlive GT or an Enlive Super are not out of question.)

Z like zombie because it's Enlive N raising from the grave.

## License

Copyright © 2019 FIXME

Distributed under the Eclipse Public License either version 1.0 or (at
your option) any later version.
