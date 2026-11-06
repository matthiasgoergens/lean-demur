module

public import Parse
-- the `#guard`s below run code from this import
meta import Parse

namespace Parse.Test

deriving instance BEq for Result

/-- `p` run on `s` from its start. -/
def run (p : P ε α) (s : String) : Result ε α := p s.toList.toArray 0

/-- A run of decimal digits, as its value. -/
def digits : P ε Nat := do
  let ds ← many1 (sat Char.isDigit)
  return ds.foldl (fun n d => 10 * n + (d.toNat - '0'.toNat)) 0

-- Reading, and where the parser stops.
#guard run (digits : P Empty Nat) "042x" == .ok 42 3
#guard run (digits : P Empty Nat) "x42" == .miss
#guard run (digits : P Empty Nat) "" == .miss
#guard run (many (ch 'a') : P Empty (List Unit)) "bbb" == .ok [] 0

-- `<|>` tries the alternative where the first rule does not apply, but a refusal is final.
#guard run ((digits <|> (do ch 'x'; return 0)) : P Empty Nat) "x" == .ok 0 1
#guard run ((do ch '-'; refuse "negative") <|> (digits : P String Nat)) "-1" == .refuse "negative"
#guard run ((do ch '-'; refuse "negative") <|> (digits : P String Nat)) "7" == .ok 7 1
-- `orMiss` turns a refusal into not applying, for use in a grammar that does not refuse.
#guard run ((orMiss (do ch '-'; (refuse "negative" : P String Nat))) <|> (digits : P Empty Nat)) "-1" ==
  .miss

-- `opt`, `ahead` and `keepPlace` read nothing where they say so.
#guard run (opt (ch '+') *> (digits : P Empty Nat)) "+5" == .ok 5 2
#guard run (opt (ch '+') *> (digits : P Empty Nat)) "5" == .ok 5 1
#guard run (ahead (digits : P Empty Nat)) "12" == .ok true 0
#guard run (keepPlace (digits : P Empty Nat)) "12" == .ok 12 0

-- `iterate` feeds each result to the next repeat.
#guard run (iterate (fun n => do ch 'i'; return n + 1) 0 : P Empty Nat) "iiix" == .ok 3 3

-- `scan` and `found`: leftmost places, none overlapping, positions in characters.
#guard found (digits : P Empty Nat) "a1 23 456".toList.toArray == #[(1, 1), (3, 23), (6, 456)]
#guard found (digits : P Empty Nat) "no digits".toList.toArray == #[]
#guard found (chars ['a', 'a']) "aaaaa".toList.toArray == #[(0, ()), (2, ())]
-- A character outside ASCII counts once, whatever its UTF-8 length.
#guard found (digits : P Empty Nat) "€5 é7".toList.toArray == #[(1, 5), (4, 7)]
-- `found` from a later start.
#guard found (digits : P Empty Nat) "1 2 3".toList.toArray 1 == #[(2, 2), (4, 3)]

-- Words standing alone: `cat` but not inside `concat` or `cats`.
#guard (found (charsAlone ['c', 'a', 't'] Char.isAlpha Char.isAlpha) "concat cat cats".toList.toArray).map
  Prod.fst == #[7]

-- Looking behind and ahead.
#guard run (behind 1 : P Empty (Option Char)) "ab" == .ok none 0
#guard run (advance *> (behind 1 : P Empty (Option Char))) "ab" == .ok (some 'a') 1
#guard run (advance *> (isAfter [(· == 'a')] : P Empty Unit)) "ab" == .ok () 1
#guard run (advance *> (isAfter [(· == 'b')] : P Empty Unit)) "ab" == .miss
#guard run (isBefore (· == 'a') : P Empty Unit) "ab" == .ok () 0
#guard run (notBefore (· == 'a') : P Empty Unit) "ab" == .miss
#guard run (advance *> advance *> (atEnd : P Empty Bool)) "ab" == .ok true 2
#guard run (peekAt 1 : P Empty (Option Char)) "ab" == .ok (some 'b') 0

-- `replaceFound` and `splitFound`.
#guard String.ofList (replaceFound (do let _ ← (digits : P Empty Nat); return ['#']) "a1b22c".toList.toArray) ==
  "a#b#c"
#guard String.ofList (replaceFound (do let _ ← (digits : P Empty Nat); return ['#']) "abc".toList.toArray) == "abc"
#guard (splitFound (do ch ','; pos) "a,bc,,d".toList.toArray).map (String.ofList ·.toList) ==
  ["a", "bc", "", "d"]

-- `ruleAt` reads at one place only.
#guard ruleAt (digits : P Empty Nat) "x12".toList.toArray 1 == some (12, 3)
#guard ruleAt (digits : P Empty Nat) "x12".toList.toArray 0 == none
