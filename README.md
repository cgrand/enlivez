# Enlive Z

## Query Maps

Many queries can be expressed by using the query-map syntax. This syntax is a mix
of pattern matching, and destructuring with a pinch of pull syntax.

Like in pattern matching (and unlike destructuring), keys are in key position: `{:first-name name}`.

Like with destructuring, one can use `:attrs` (think `:keys`) and `:or` (and don't forget key val order is inverted):

```clj
{[first-name last-name] :attrs}
; is equivalent to
 {:first-name first-name :last-name last-name}

{[first last] :name/keys}
; is equivalent to
{[:name/first :name/last] :attrs}
; which is equivalent to
{:name/first first
 :name/last last}
 
; defaults can be provided 
{[first last] :name/keys
 {first "John" last "Does"} :or}
```
Note that `:attrs` must not be used recursively.

There's no `:as` because only entities can patterned, so if you want a reference to the entity just match its `:db/id` attribute!

```clj
{:family/_parent child}
; and it workq with :attrs too
{[_parent]  :family/keys}
; or
{[:family/_parent]  :attrs}
```

## Why this Z ?

Z because a Z is a sideways N. Enlive Z achieves the goals that were set for the failed Enlive N.

Z like (Zeno) [lien vers Zeno et le tarpit].

Z to pay homage to Mazinger Z and Dragon Ball Z. (So an Enlive GT or an Enlive Super are not out of question.)

Z like zombie because it's Enlive N raising from the grave.

## License

Copyright © 2019 FIXME

Distributed under the Eclipse Public License either version 1.0 or (at
your option) any later version.
