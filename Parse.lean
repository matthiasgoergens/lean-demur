module

public section

namespace Parse

/-! # Parser combinators over a text's characters

A small kit for reading text by a grammar written as code, instead of a hand loop over positions
that emulates a regular expression.  A rule (`P ε α`) is run on the characters from a place.  It
ends somewhere with what it read; or it does not apply there (`miss`), and an alternative (`<|>`)
is tried from the same place; or it refuses the words with a reason of type `ε` (`refuse`), which
is final: no alternative is tried.  A grammar that never refuses fixes `ε` to `Empty`.

The rules are written in `do` notation (`←` reads, `<|>` chooses, `many` and `iterate` repeat), and `scan` finds
the places a rule applies in a text.  Positions are counts of characters (Unicode scalar values), not
bytes. -/

/-- A text's characters, as a grammar walks them. -/
abbrev Chars := Array Char

/-- How a rule ends: what it read and where it stopped, or that it does not apply, or that the
words are refused for a reason. -/
inductive Result (ε α : Type) where
  | ok (a : α) (pos : Nat)
  | miss
  | refuse (why : ε)

/-- A rule of a grammar, run on the words from a place. -/
@[expose] def P (ε α : Type) : Type := Chars → Nat → Result ε α

instance : Monad (P ε) where
  pure a := fun _ i => .ok a i
  bind p f := fun t i =>
    match p t i with
    | .ok a j => f a t j
    | .miss => .miss
    | .refuse why => .refuse why

/-- `p`, or `q` from the same place where `p` does not apply. -/
instance : OrElse (P ε α) where
  orElse p q := fun t i =>
    match p t i with
    | .miss => q () t i
    | r => r

/-- The rule that does not apply. -/
def miss : P ε α := fun _ _ => .miss

/-- The words refused, for `why`. -/
def refuse (why : ε) : P ε α := fun _ _ => .refuse why

/-- Where the parser stands. -/
def pos : P ε Nat := fun _ i => .ok i i

/-- The words. -/
def text : P ε Chars := fun t i => .ok t i

/-- The character `k` places on, none past the end. -/
def peekAt (k : Nat) : P ε (Option Char) := fun t i => .ok t[i + k]? i

/-- The character where the parser stands, none at the end. -/
def peek : P ε (Option Char) := peekAt 0

/-- The character `k` places back (`k` at least 1), none before the start. -/
def behind (k : Nat) : P ε (Option Char) := fun t i => .ok (if k ≤ i then t[i - k]? else none) i

/-- The parser at the end of the words. -/
def atEnd : P ε Bool := fun t i => .ok (i ≥ t.size) i

/-- A character that satisfies `p`. -/
def sat (p : Char → Bool) : P ε Char := fun t i =>
  match t[i]? with
  | some c => if p c then .ok c (i + 1) else .miss
  | none => .miss

/-- A character `f` reads as a value, as that value (`satSome_ok`). -/
def satSome (f : Char → Option α) : P ε α := fun t i =>
  match t[i]? with
  | some c => match f c with
    | some a => .ok a (i + 1)
    | none => .miss
  | none => .miss

/-- The character `c`. -/
def ch (c : Char) : P ε Unit := discard (sat (· == c))

/-- Any one character. -/
def advance : P ε Unit := discard (sat fun _ => true)

/-- `p`, or none with nothing read where `p` does not apply; a refusal inside `p` is final. -/
def opt (p : P ε α) : P ε (Option α) := (some <$> p) <|> pure none

/-- Whether `p` applies here; nothing is read, and a refusal inside `p` is final. -/
def ahead (p : P ε α) : P ε Bool := fun t i =>
  match p t i with
  | .ok _ _ => .ok true i
  | .miss => .ok false i
  | .refuse why => .refuse why

/-- `p`, the parser left where it was. -/
def keepPlace (p : P ε α) : P ε α := fun t i =>
  match p t i with
  | .ok a _ => .ok a i
  | r => r

/-- `p` with its refusals taken as not applying: a rule of a grammar that refuses, used in one that
does not. -/
def orMiss (p : P ε α) : P ε' α := fun t i =>
  match p t i with
  | .ok a j => .ok a j
  | _ => .miss

/-- `p` as often as it applies, none too: until it does not apply, or applies reading nothing, or
the end of the words is passed. -/
def many (p : P ε α) : P ε (List α) := fun t i => go t i #[]
where
  /-- The repeats from `j` on, after `out`. -/
  go (t : Chars) (j : Nat) (out : Array α) : Result ε (List α) :=
    if j ≤ t.size then
      match p t j with
      | .ok a k => if k ≤ j then .ok (out.push a).toList j else go t k (out.push a)
      | .miss => .ok out.toList j
      | .refuse why => .refuse why
    else .ok out.toList j
  termination_by t.size + 1 - j

/-- `p` again and again, each time on what it read the time before, from `a`: what it read last, or
`a` where it does not apply at all.  As `many`, it stops where `p` does not apply, or applies reading
nothing, or the end of the words is passed. -/
def iterate (p : α → P ε α) (a : α) : P ε α := fun t i => go t i a
where
  /-- The repeats from `j` on, after `a`. -/
  go (t : Chars) (j : Nat) (a : α) : Result ε α :=
    if j ≤ t.size then
      match p a t j with
      | .ok b k => if k ≤ j then .ok b j else go t k b
      | .miss => .ok a j
      | .refuse why => .refuse why
    else .ok a j
  termination_by t.size + 1 - j

/-- `p` as often as it applies, once at least. -/
def many1 (p : P ε α) : P ε (List α) := do
  let xs ← many p
  if xs.isEmpty then miss
  return xs

/-- Each place from here where `p` applies, with what it read, leftmost first and none
overlapping: a place where `p` does not apply is passed one character on, one where it applies
is passed whole.  The places are in the words, up to the place just past the last character. -/
def scan (p : P ε α) : P ε (Array (Nat × α)) := fun t i => go t i #[]
where
  /-- The places from `j` on, after `out`. -/
  go (t : Chars) (j : Nat) (out : Array (Nat × α)) : Result ε (Array (Nat × α)) :=
    if j ≤ t.size then
      match p t j with
      | .ok a k => go t (max k (j + 1)) (out.push (j, a))
      | .miss => go t (j + 1) out
      | .refuse why => .refuse why
    else .ok out j
  termination_by t.size + 1 - j

/-- Each place in `t` from `start` on where `p`, a rule that never refuses, applies, with what it
read (`scan`). -/
def found (p : P Empty α) (t : Chars) (start : Nat := 0) : Array (Nat × α) :=
  match scan p t start with
  | .ok places _ => places
  | .miss => #[]
  | .refuse why => nomatch why

/-- `t` with each place `p` applies (`found`) replaced by what `p` reads there, the rest as it
stands. -/
def replaceFound (p : P Empty (List Char)) (t : Chars) : List Char :=
  let places := found (do let r ← p; return (r, ← pos)) t
  let (out, last) := places.foldl (fun (out, last) (s, r, e) => (out ++ (t.extract last s).toList ++ r, e)) ([], 0)
  out ++ (t.extract last t.size).toList

/-- What `p`, a rule that never refuses, reads from `i` of `t` and where it stops, when it applies
there. -/
def ruleAt (p : P Empty α) (t : Chars) (i : Nat) : Option (α × Nat) :=
  match p t i with
  | .ok a j => some (a, j)
  | _ => none

/-- `t` cut at each place `p` applies (`found`), what it reads there left out: the pieces before,
between and after those places.  `p` reads where it ends. -/
@[expose] def splitFound (p : P Empty Nat) (t : Chars) : List (Array Char) :=
  let cuts := (found p t).toList
  ((0 :: cuts.map Prod.snd).zip (cuts.map Prod.fst ++ [t.size])).map fun ab => t.extract ab.1 ab.2

/-- The characters `cs`, in order. -/
def chars : List Char → P ε Unit
  | [] => pure ()
  | c :: cs => ch c *> chars cs

/-- Nothing read, where the character right before is not one `q` holds of (or there is none). -/
def notAfter (q : Char → Bool) : P ε Unit := fun t i =>
  if 0 < i && t[i - 1]?.any q then .miss else .ok () i

/-- Nothing read, where the character here is not one `q` holds of (or there is none). -/
def notBefore (q : Char → Bool) : P ε Unit := fun t i =>
  if t[i]?.any q then .miss else .ok () i

/-- Nothing read, right after characters `qs` hold of, one each, in order. -/
def isAfter (qs : List (Char → Bool)) : P ε Unit := fun t i =>
  if qs.length ≤ i && i ≤ t.size && ((t.extract (i - qs.length) i).toList.zipWith (fun c q => q c) qs).all id then
    .ok () i
  else .miss

/-- Nothing read, where the character here is one `q` holds of. -/
def isBefore (q : Char → Bool) : P ε Unit := fun t i =>
  if t[i]?.any q then .ok () i else .miss

/-- The characters `cs`, not right after a character `before` holds of, nor right before one
`after` holds of: a word standing on its own, for the meaning of word those say. -/
def charsAlone (cs : List Char) (before after : Char → Bool) : P ε Unit :=
  notAfter before *> chars cs *> notBefore after

/-! ## What the rules read -/

/-- Two places `scan` found, in order: the second lies past the first, and past where `p` stopped
at the first. -/
@[expose] def Apart (p : P ε α) (t : Chars) (x y : Nat × α) : Prop :=
  x.1 < y.1 ∧ ∀ k, p t x.1 = .ok x.2 k → k ≤ y.1

/-- A place `scan` found from `start`: in the words, and `p` applies there with what was found. -/
@[expose] def Applies (p : P ε α) (t : Chars) (start : Nat) (x : Nat × α) : Prop :=
  start ≤ x.1 ∧ x.1 ≤ t.size ∧ ∃ k, p t x.1 = .ok x.2 k

private theorem scan_go_sound (p : P ε α) (t : Chars) (start : Nat) :
    ∀ (j : Nat) (out : Array (Nat × α)), start ≤ j → out.toList.Pairwise (Apart p t) →
      (∀ x ∈ out, Applies p t start x) → (∀ x ∈ out, x.1 < j ∧ ∀ k, p t x.1 = .ok x.2 k → k ≤ j) →
      ∀ out' j', scan.go p t j out = .ok out' j' →
      out'.toList.Pairwise (Apart p t) ∧ ∀ x ∈ out', Applies p t start x := by
  intro j out
  induction j, out using scan.go.induct p t with
  | case1 j out inside a k applies ih =>
    intro hstart hpair happ hbelow out' j' h
    rw [scan.go, ite_eq_left inside, applies] at h
    refine ih (by omega) ?_ ?_ ?_ out' j' h
    · simp only [Array.toList_push, List.pairwise_append, List.pairwise_singleton, List.mem_singleton,
        forall_eq, true_and]
      exact ⟨hpair, fun x hx => (hbelow x (by simpa using hx))⟩
    · intro x hx
      rcases Array.mem_push.mp hx with hx | rfl
      · exact happ x hx
      · exact ⟨hstart, inside, k, applies⟩
    · intro x hx
      rcases Array.mem_push.mp hx with hx | rfl
      · have := hbelow x hx
        exact ⟨by omega, fun k' hk => by have := this.2 k' hk; omega⟩
      · refine ⟨by omega, fun k' hk => ?_⟩
        rw [applies] at hk
        cases hk
        omega
  | case2 j out inside misses ih =>
    intro hstart hpair happ hbelow out' j' h
    rw [scan.go, ite_eq_left inside, misses] at h
    refine ih (by omega) hpair happ ?_ out' j' h
    intro x hx
    have := hbelow x hx
    exact ⟨by omega, fun k' hk => by have := this.2 k' hk; omega⟩
  | case3 j out inside why refuses =>
    intro _ _ _ _ out' j' h
    rw [scan.go, ite_eq_left inside, refuses] at h
    cases h
  | case4 j out outside =>
    intro _ hpair happ _ out' j' h
    rw [scan.go, ite_eq_right outside] at h
    cases h
    exact ⟨hpair, happ⟩

/-- What `scan` finds from `start`: places in the words from `start` on, where `p` applies with
what was found, each past the one before and past where `p` stopped there. -/
theorem scan_sound (p : P ε α) (t : Chars) (start : Nat) {out : Array (Nat × α)} {stop : Nat}
    (h : scan p t start = .ok out stop) :
    out.toList.Pairwise (Apart p t) ∧ ∀ x ∈ out, Applies p t start x :=
  scan_go_sound p t start start #[] (Nat.le_refl _) (by simp) (by simp) (by simp) out stop h

/-- What `found` finds from `start`, as `scan` does (`scan_sound`). -/
theorem found_sound (p : P Empty α) (t : Chars) (start : Nat) :
    (found p t start).toList.Pairwise (Apart p t) ∧ ∀ x ∈ found p t start, Applies p t start x := by
  unfold found
  split
  · next h => exact scan_sound p t start h
  · simp
  · next why _ => exact nomatch why

/-- Where `satSome f` reads from `i`: the character there, which `f` reads as what it gives, and it
stops past it. -/
theorem satSome_ok (f : Char → Option α) (t : Chars) (i : Nat) {a : α} {k : Nat}
    (h : (satSome f : P ε α) t i = .ok a k) : ∃ c, t[i]? = some c ∧ f c = some a ∧ k = i + 1 := by
  simp only [satSome] at h
  split at h
  · next c here =>
    split at h
    · next found =>
      cases h
      exact ⟨c, here, found, rfl⟩
    · cases h
  · cases h

/-- Where `chars cs` reads from `i`: the characters from there are `cs`, and it stops past them. -/
theorem chars_ok (cs : List Char) (t : Chars) (i : Nat) {u : Unit} {k : Nat}
    (h : (chars cs : P ε Unit) t i = .ok u k) : ∃ post, t.toList.drop i = cs ++ post ∧ k = i + cs.length := by
  induction cs generalizing i with
  | nil =>
    cases h
    exact ⟨_, rfl, rfl⟩
  | cons c cs ih =>
    simp only [chars, ch, sat, Functor.discard, SeqRight.seqRight, Functor.mapConst, Function.comp] at h
    cases here : t[i]? with
    | none => simp [here] at h
    | some d =>
      by_cases same : d = c
      · subst same
        simp only [here, BEq.rfl, ite_true] at h
        obtain ⟨post, rest, stop⟩ := ih (i + 1) h
        refine ⟨post, ?_, by simp [stop]; omega⟩
        obtain ⟨inside, value⟩ := Array.getElem?_eq_some_iff.mp here
        rw [List.drop_eq_getElem_cons (l := t.toList) (i := i) (by simpa using inside), rest]
        simp [value]
      · simp [here, same] at h

/-- Where `charsAlone cs before after` applies from `i`: the text is `cs` between a part that does
not end in a character `before` holds of and one that does not start with one `after` holds of. -/
theorem charsAlone_ok (cs : List Char) (before after : Char → Bool) (t : Chars) (i : Nat) {u : Unit} {k : Nat}
    (inside : i ≤ t.size) (h : (charsAlone cs before after : P ε Unit) t i = .ok u k) :
    ∃ pre post, t.toList = pre ++ cs ++ post ∧ i = pre.length ∧ k = i + cs.length ∧
      pre.getLast?.all (!before ·) ∧ post.head?.all (!after ·) := by
  simp only [charsAlone, SeqRight.seqRight] at h
  split at h
  · next j read =>
    split at read
    · next free =>
      simp only [notAfter] at free
      split at free
      · cases free
      · next free' =>
        cases free
        simp only [notBefore] at h
        split at h
        · cases h
        · next clear =>
          cases h
          obtain ⟨post, rest, stop⟩ := chars_ok cs t i read
          refine ⟨t.toList.take i, post, ?_, by simp; omega, stop, ?_, ?_⟩
          · rw [List.append_assoc, ← rest, List.take_append_drop]
          · rw [List.getLast?_take]
            by_cases zero : i = 0
            · simp [zero]
            · have lt : i - 1 < t.size := by omega
              have last : t.toList[i - 1]? = some t[i - 1] := by simp [lt]
              have own : t[i - 1]? = some t[i - 1] := by simp [lt]
              simp only [zero, ite_false, last]
              simp only [own, show 0 < i by omega, decide_true, Bool.true_and] at free'
              simpa using free'
          · have := congrArg (List.drop cs.length) rest
            rw [List.drop_drop, List.drop_left] at this
            rw [← this, List.head?_drop, Array.getElem?_toList, ← stop]
            cases here : t[k]? with
            | none => rfl
            | some c => simpa [here] using clear
    · cases read
    · cases read
  · cases h
  · cases h

/-- Where `p >>= f` applies, `p` applies first, and `f` from where it stopped. -/
theorem bind_ok {p : P ε α} {f : α → P ε β} {t : Chars} {i : Nat} {b : β} {k : Nat}
    (h : (p >>= f) t i = .ok b k) : ∃ a j, p t i = .ok a j ∧ f a t j = .ok b k := by
  change (match p t i with | .ok a j => f a t j | .miss => .miss | .refuse why => .refuse why) = _ at h
  split at h
  · exact ⟨_, _, ‹_›, h⟩
  · cases h
  · cases h

/-- Where `p` applies nowhere in `t`, `replaceFound` leaves it as it stands. -/
theorem replaceFound_none (p : P Empty (List Char)) (t : Chars)
    (nowhere : ∀ j ≤ t.size, ∀ r k, p t j ≠ .ok r k) : replaceFound p t = t.toList := by
  have empty : found (do let r ← p; return (r, ← pos)) t = #[] := by
    obtain ⟨_, applies⟩ := found_sound (do let r ← p; return (r, ← pos)) t 0
    apply Array.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨_, inside, k, h⟩ := applies x hx
    obtain ⟨_, _, applied, _⟩ := bind_ok h
    exact nowhere x.1 inside _ _ applied
  simp [replaceFound, empty]

/-- Where `many (sat q)` reads from `j`, after `out`, which it read from `i` and holds of: every
character from `i` to where it stops is one `q` holds of, it stops within the words, and it reads a
character for each place it moves on. -/
private theorem many_sat_go (q : Char → Bool) (t : Chars) (i : Nat) :
    ∀ (j : Nat) (out : Array Char), i ≤ j → j ≤ t.size →
      (∀ m (inside : m < t.size), i ≤ m → m < j → q t[m] = true) →
      t.toList.drop i = out.toList ++ t.toList.drop j → (∀ c ∈ out, q c = true) →
      ∀ cs k, many.go (sat q : P ε Char) t j out = .ok cs k →
      j ≤ k ∧ out.size + (k - j) = cs.length ∧ k ≤ t.size ∧
        (∀ m (inside : m < t.size), i ≤ m → m < k → q t[m] = true) ∧
        t.toList.drop i = cs ++ t.toList.drop k ∧ ∀ c ∈ cs, q c = true := by
  intro j out
  induction j, out using many.go.induct (sat q : P ε Char) t with
  | case1 j out _ a k applies stays =>
    intro _ _ _ _ _ cs k' _
    simp only [sat] at applies
    split at applies
    · split at applies
      · cases applies; omega
      · cases applies
    · cases applies
  | case2 j out _ a k applies moves ih =>
    intro hi hj hq hl hout cs k' h
    rw [many.go, ite_eq_left ‹_›, applies] at h
    dsimp only at h
    rw [ite_eq_right moves] at h
    simp only [sat] at applies
    split at applies
    · next c here =>
      split at applies
      · next holds =>
        cases applies
        obtain ⟨inside, value⟩ := Array.getElem?_eq_some_iff.mp here
        have hl' : t.toList.drop i = (out.push a).toList ++ t.toList.drop (j + 1) := by
          rw [hl, List.drop_eq_getElem_cons (l := t.toList) (i := j) (by simpa using inside)]
          simp [value]
        have hout' : ∀ d ∈ out.push a, q d = true := by
          intro d hd
          rcases Array.mem_push.mp hd with hd | rfl
          · exact hout d hd
          · simpa using holds
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih (by omega) (by omega) (fun m hm h1 h2 => by
          by_cases e : m = j
          · subst e; simpa [value] using holds
          · exact hq m hm h1 (by omega)) hl' hout' cs k' h
        refine ⟨by omega, ?_, h3, h4, h5, h6⟩
        simp only [Array.size_push] at h2
        omega
      · cases applies
    · cases applies
  | case3 j out _ applies =>
    intro hi hj hq hl hout cs k h
    rw [many.go, ite_eq_left ‹_›, applies] at h
    cases h
    exact ⟨Nat.le_refl _, by simp, hj, hq, hl, fun c hc => hout c (by simpa using hc)⟩
  | case4 j out _ why applies =>
    intro _ _ _ _ _ cs k h
    rw [many.go, ite_eq_left ‹_›, applies] at h
    cases h
  | case5 j out outside =>
    intro _ hj _ _ _ _ _ _
    exact absurd hj outside

/-- Where `many1 (sat q)` reads from `i`: at least one character, each one `q` holds of, the characters
from `i` to where it stops, within the words. -/
theorem many1_sat_ok (q : Char → Bool) (t : Chars) (i : Nat) {cs : List Char} {k : Nat}
    (h : (many1 (sat q) : P ε (List Char)) t i = .ok cs k) :
    i < k ∧ k ≤ t.size ∧ (∀ m (inside : m < t.size), i ≤ m → m < k → q t[m] = true) ∧
      t.toList.drop i = cs ++ t.toList.drop k ∧ cs ≠ [] ∧ ∀ c ∈ cs, q c = true := by
  simp only [many1] at h
  obtain ⟨xs, j, read, h⟩ := bind_ok h
  by_cases e : xs.isEmpty = true
  · simp only [e, ite_true] at h
    obtain ⟨_, _, missed, _⟩ := bind_ok h
    cases missed
  · simp only [e, Bool.false_eq_true, ite_false] at h
    cases h
    unfold many at read
    by_cases inside : i ≤ t.size
    · obtain ⟨_, length, stop, holds, rest, each⟩ := many_sat_go q t i i #[] (Nat.le_refl _) inside
        (fun _ _ h1 h2 => absurd h2 (by omega)) (by simp) (by simp) cs k read
      have : cs.length ≠ 0 := by simpa [List.isEmpty_iff] using e
      refine ⟨?_, stop, holds, rest, by simpa [List.isEmpty_iff] using e, each⟩
      simp at length
      omega
    · rw [many.go, ite_eq_right inside] at read
      cases read
      simp at e

/-- `pos` reads nothing and yields where it stands. -/
theorem pos_ok {t : Chars} {i a k : Nat} (h : (pos : P ε Nat) t i = .ok a k) : a = i ∧ k = i := by
  cases h; exact ⟨rfl, rfl⟩

/-- `isAfter` reads nothing. -/
theorem isAfter_ok {qs : List (Char → Bool)} {t : Chars} {i : Nat} {u : Unit} {k : Nat}
    (h : (isAfter qs : P ε Unit) t i = .ok u k) : k = i := by
  simp only [isAfter] at h
  split at h
  · cases h; rfl
  · cases h

/-- `isBefore q` reads nothing, and applies before a character of the words. -/
theorem isBefore_ok {q : Char → Bool} {t : Chars} {i : Nat} {u : Unit} {k : Nat}
    (h : (isBefore q : P ε Unit) t i = .ok u k) : k = i ∧ i < t.size := by
  simp only [isBefore] at h
  split at h
  · next here =>
    cases h
    refine ⟨rfl, ?_⟩
    cases e : t[i]? with
    | none => simp [e] at here
    | some c => exact (Array.getElem?_eq_some_iff.mp e).1
  · cases h

/-- `notAfter q` reads nothing, and applies where the text before does not end in a character `q`
holds of. -/
theorem notAfter_ok {q : Char → Bool} {t : Chars} {i : Nat} {u : Unit} {k : Nat} (inside : i ≤ t.size)
    (h : (notAfter q : P ε Unit) t i = .ok u k) : k = i ∧ (t.toList.take i).getLast?.all (!q ·) := by
  simp only [notAfter] at h
  split at h
  · cases h
  · next free =>
    cases h
    refine ⟨rfl, ?_⟩
    rw [List.getLast?_take]
    by_cases zero : i = 0
    · simp [zero]
    · have lt : i - 1 < t.size := by omega
      have last : t.toList[i - 1]? = some t[i - 1] := by simp [lt]
      have own : t[i - 1]? = some t[i - 1] := by simp [lt]
      simp only [zero, ite_false, last]
      simp only [own, show 0 < i by omega, decide_true, Bool.true_and] at free
      simpa using free

/-- `notBefore q` reads nothing, and applies where the text after does not start with a character
`q` holds of. -/
theorem notBefore_ok {q : Char → Bool} {t : Chars} {i : Nat} {u : Unit} {k : Nat}
    (h : (notBefore q : P ε Unit) t i = .ok u k) : k = i ∧ (t.toList.drop i).head?.all (!q ·) := by
  simp only [notBefore] at h
  split at h
  · cases h
  · next clear =>
    cases h
    refine ⟨rfl, ?_⟩
    rw [List.head?_drop, Array.getElem?_toList]
    cases here : t[i]? with
    | none => rfl
    | some c => simpa [here] using clear

/-- `ch c` reads the character `c`. -/
theorem ch_ok {c : Char} {t : Chars} {i : Nat} {u : Unit} {k : Nat}
    (h : (ch c : P ε Unit) t i = .ok u k) : k = i + 1 ∧ t.toList.drop i = c :: t.toList.drop (i + 1) := by
  simp only [ch, sat, Functor.discard, Functor.mapConst, Function.comp] at h
  cases here : t[i]? with
  | none => simp [here] at h
  | some d =>
    by_cases same : d = c
    · subst same
      simp only [here, BEq.rfl, ite_true] at h
      cases h
      obtain ⟨inside, value⟩ := Array.getElem?_eq_some_iff.mp here
      refine ⟨rfl, ?_⟩
      rw [List.drop_eq_getElem_cons (l := t.toList) (i := i) (by simpa using inside)]
      simp [value]
    · simp [here, same] at h

/-! ## Where the rules apply

The converse of the lemmas above: from what the words hold, where a rule applies and what it reads,
so that a proof can show that a rule finds what it should (`found_at_start`). -/

/-- Where `p` applies from `i`, stopping at `j` with `a`, `p >>= f` goes on with `f a` from `j`. -/
theorem bind_of_ok {p : P ε α} {f : α → P ε β} {t : Chars} {i : Nat} {a : α} {j : Nat}
    (h : p t i = .ok a j) : (p >>= f) t i = f a t j := by
  change (match p t i with | .ok a j => f a t j | .miss => .miss | .refuse why => .refuse why) = _
  rw [h]

/-- The character at `i`, read from the words from `i` on. -/
private theorem getElem?_of_drop {t : Chars} {i : Nat} {c : Char} {rest : List Char}
    (h : t.toList.drop i = c :: rest) : t[i]? = some c := by
  have := congrArg List.head? h
  rw [List.head?_drop, Array.getElem?_toList] at this
  simpa using this

/-- `sat q` reads the character the words from `i` start with, where `q` holds of it. -/
private theorem sat_of_drop {q : Char → Bool} {t : Chars} {i : Nat} {c : Char} {rest : List Char}
    (h : t.toList.drop i = c :: rest) (holds : q c = true) : (sat q : P ε Char) t i = .ok c (i + 1) := by
  simp [sat, getElem?_of_drop h, holds]

/-- `sat q` does not apply where the words from `i` are at their end, or start with a character `q`
does not hold of. -/
private theorem sat_miss {q : Char → Bool} {t : Chars} {i : Nat} {rest : List Char}
    (h : t.toList.drop i = rest) (stops : rest.head?.all (!q ·) = true) : (sat q : P ε Char) t i = .miss := by
  cases rest with
  | nil =>
    have : t[i]? = none := by
      have := congrArg List.head? h
      rw [List.head?_drop, Array.getElem?_toList] at this
      simpa using this
    simp [sat, this]
  | cons c rest =>
    simp only [List.head?_cons, Option.all_some, Bool.not_eq_eq_eq_not, Bool.not_true] at stops
    simp [sat, getElem?_of_drop h, stops]

/-- `many (sat q)` from `j`, after `out`, reads the characters `cs` the words from `j` start with, each
one `q` holds of, where what follows them is the end or a character `q` does not hold of. -/
private theorem many_sat_reads (q : Char → Bool) (t : Chars) :
    ∀ (cs : List Char) (j : Nat) (out : Array Char) (rest : List Char),
      t.toList.drop j = cs ++ rest → (∀ c ∈ cs, q c = true) → rest.head?.all (!q ·) = true →
      many.go (sat q : P ε Char) t j out = .ok (out.toList ++ cs) (j + cs.length) := by
  intro cs
  induction cs with
  | nil =>
    intro j out rest h _ stops
    rw [List.nil_append] at h
    rw [many.go]
    split
    · rw [sat_miss h stops]; simp
    · simp
  | cons c cs ih =>
    intro j out rest h holds stops
    rw [List.cons_append] at h
    have inside : j < t.size := (Array.getElem?_eq_some_iff.mp (getElem?_of_drop h)).1
    have next : t.toList.drop (j + 1) = cs ++ rest := by
      rw [← List.tail_drop, h]; rfl
    rw [many.go, ite_eq_left (by omega), sat_of_drop h (holds c (by simp))]
    dsimp only
    rw [ite_eq_right (by omega), ih (j + 1) (out.push c) rest next (fun d hd => holds d (by simp [hd])) stops]
    congr 1
    · simp
    · simp only [List.length_cons]; omega

/-- `many1 (sat q)` from `i` reads the characters `cs`, one at least, the words from `i` start with,
each one `q` holds of, where what follows them is the end or a character `q` does not hold of. -/
theorem many1_sat_reads (q : Char → Bool) (t : Chars) (i : Nat) {cs rest : List Char}
    (h : t.toList.drop i = cs ++ rest) (ne : cs ≠ []) (holds : ∀ c ∈ cs, q c = true)
    (stops : rest.head?.all (!q ·) = true) :
    (many1 (sat q) : P ε (List Char)) t i = .ok cs (i + cs.length) := by
  have read : (many (sat q) : P ε (List Char)) t i = .ok cs (i + cs.length) := by
    show many.go (sat q) t i #[] = _
    simpa using many_sat_reads q t cs i #[] rest h holds stops
  have full : cs.isEmpty = false := by cases cs <;> simp_all
  unfold many1
  rw [bind_of_ok read]
  simp only [full, Bool.false_eq_true, ite_false]
  rfl

/-- `scan` of a rule that never refuses ends, and keeps each place found before it went on. -/
private theorem scan_go_keeps (p : P Empty α) (t : Chars) :
    ∀ (j : Nat) (out : Array (Nat × α)),
      ∃ out' j', scan.go p t j out = .ok out' j' ∧ ∀ x ∈ out, x ∈ out' := by
  intro j out
  induction j, out using scan.go.induct p t with
  | case1 j out inside a k applies ih =>
    obtain ⟨out', j', h, keep⟩ := ih
    refine ⟨out', j', ?_, fun x hx => keep x (Array.mem_push.mpr (.inl hx))⟩
    rw [scan.go, ite_eq_left inside, applies]
    exact h
  | case2 j out inside misses ih =>
    obtain ⟨out', j', h, keep⟩ := ih
    refine ⟨out', j', ?_, keep⟩
    rw [scan.go, ite_eq_left inside, misses]
    exact h
  | case3 j out inside why refuses => exact why.elim
  | case4 j out outside =>
    exact ⟨out, j, by rw [scan.go, ite_eq_right outside], fun x hx => hx⟩

/-- Where a rule that never refuses applies at the start of the words, `found` finds it there. -/
theorem found_at_start (p : P Empty α) (t : Chars) {a : α} {k : Nat} (applies : p t 0 = .ok a k) :
    (0, a) ∈ found p t := by
  obtain ⟨out', j', h, keep⟩ := scan_go_keeps p t (max k (0 + 1)) (#[].push (0, a))
  have scanned : scan p t 0 = .ok out' j' := by
    show scan.go p t 0 #[] = _
    rw [scan.go, ite_eq_left (Nat.zero_le _), applies]
    exact h
  unfold found
  rw [scanned]
  exact keep _ (by simp)

/-- `notAfter q` applies at the start of the words, which has no character before it. -/
theorem notAfter_start {q : Char → Bool} {t : Chars} : (notAfter q : P ε Unit) t 0 = .ok () 0 := by
  simp [notAfter]

/-- `notBefore q` applies at the end of the words, which has no character after it. -/
theorem notBefore_end {q : Char → Bool} {t : Chars} {i : Nat} (past : t.size ≤ i) :
    (notBefore q : P ε Unit) t i = .ok () i := by
  simp [notBefore, Array.getElem?_eq_none past]

/-- `ch c` reads the character `c` where the words from `i` start with it. -/
theorem ch_of_drop {c : Char} {t : Chars} {i : Nat} {rest : List Char} (h : t.toList.drop i = c :: rest) :
    (ch c : P ε Unit) t i = .ok () (i + 1) := by
  simp [ch, sat, Functor.discard, Functor.mapConst, Function.comp, getElem?_of_drop h]
