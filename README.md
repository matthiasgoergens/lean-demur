# Parse

Parser combinators for Lean 4, on the toolchain alone (no Mathlib, no Batteries), in which a rule ends in one of three ways: it reads something and says where it stopped; it does not apply (`miss`), so an alternative is tried from the same place; or it refuses the text with a reason of a type you choose (`refuse`), which is final: no alternative is tried.  A grammar that never refuses fixes the reason type to `Empty`.

The distinction between "this rule does not apply here" and "this text is wrong" is what Lean's own `Std.Internal.Parsec` lacks, and it is what a grammar needs to report a typed error rather than backtrack past it.

```lean
import Parse
open Parse

def digits : P ε Nat := do
  let ds ← many1 (sat Char.isDigit)
  return ds.foldl (fun n d => 10 * n + (d.toNat - '0'.toNat)) 0

#eval found (digits : P Empty Nat) "a1 23 456".toList.toArray
-- #[(1, 1), (3, 23), (6, 456)]
```

Rules are written in `do` notation: `←` reads, `<|>` chooses, `many`, `many1` and `iterate` repeat, `opt`, `ahead` and `keepPlace` look without committing, and `notAfter`, `notBefore`, `isAfter`, `isBefore` and `behind` look at the characters around a place.  `scan` and `found` give every place in a text where a rule applies, leftmost first and none overlapping; `replaceFound` and `splitFound` rewrite or cut a text at those places.

Every function is total: the repeating combinators stop on a measure, without fuel, and stop where a rule applies but reads nothing.  Theorems state what the basic rules read (`ch_ok`, `many1_sat_ok`, `bind_ok`, ...) and that `found` returns only places where the rule applies, in order and apart (`found_sound`), so a grammar built on them can be reasoned about.

## Use

In `lakefile.lean`:

```lean
require parse from git "https://github.com/matthiasgoergens/lean-parse" @ "<commit>"
```

or in `lakefile.toml`:

```toml
[[require]]
name = "parse"
git = "https://github.com/matthiasgoergens/lean-parse"
rev = "<commit>"
```

The toolchain is in `lean-toolchain`.  `lake test` runs the examples in `Parse/Test.lean`.

## Limits

The input is an `Array Char`, and positions are counts of characters, not UTF-8 byte offsets: a caller first turns its `String` into an array (`s.toList.toArray`).  Running directly on a `String` is planned.

## Licence

Apache License 2.0; see `LICENSE`.
