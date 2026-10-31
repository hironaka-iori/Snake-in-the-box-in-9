import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0



/-!
# Interface between snake geometry and local window certificates

The window certificates of `milestones/10-window-aggregate/` refute CNFs on the
radius-three ball around a window of consecutive path vertices.  This module fixes
the abstract statement that connects the two sides:

* `Axioms S E window centres` lists the necessary conditions that the vertex set `S`
  of a snake (after a cube automorphism moving the window to canonical position) and
  its endpoint set `E` satisfy.  Every clause family of the local CNF follows from
  these conditions.
* A certificate module proves `∀ S E, Axioms S E window centres → False` for one
  canonical window, by a kernel-checked refutation of the CNF.
* The bridge proves `Axioms` for every snake window in canonical position.

Vertices are natural numbers below 512, so kernel evaluation stays on `Nat`.
-/

namespace Snake9.LocalWindow

/-- Hypercube neighbours of `v` in Q9. -/
def nbrs (v : Nat) : List Nat := (List.range 9).map (fun k => v ^^^ (1 <<< k))

/-- Number of entries of `l` satisfying `S` (with multiplicity). -/
def cnt (S : Nat → Bool) (l : List Nat) : Nat := (l.filter S).length

/-- Coordinate pairs `(a,b)` with `a < b < 9` avoiding the directions `d₁`, `d₂`. -/
def freePairs (d₁ d₂ : Nat) : List (Nat × Nat) :=
  (List.range 9).flatMap fun a => (List.range 9).filterMap fun b =>
    if a < b ∧ a ≠ d₁ ∧ a ≠ d₂ ∧ b ≠ d₁ ∧ b ≠ d₂ then some (a, b) else none

/-- Absent opposite corners `c ⊕ e_a ⊕ e_b` over the free pairs.  At an internal path
vertex with path directions `d₁ ≠ d₂` this is its singleton-square count. -/
def absentCorners (S : Nat → Bool) (c d₁ d₂ : Nat) : Nat :=
  ((freePairs d₁ d₂).filter fun ab => !S (c ^^^ (1 <<< ab.1) ^^^ (1 <<< ab.2))).length

/-- A window centre: the vertex, its two path directions, and bounds on its count. -/
structure Centre where
  v : Nat
  d₁ : Nat
  d₂ : Nat
  lo : Nat
  hi : Nat
deriving Repr, DecidableEq

/-- Necessary conditions on the (normalized) vertex set `S` and endpoint set `E` of a
snake that contains the vertices of `window`, whose centres have the given counts. -/
structure Axioms (S E : Nat → Bool) (window : List Nat) (centres : List Centre) : Prop where
  window_sel : ∀ v ∈ window, S v = true
  sel_lt : ∀ v, S v = true → v < 512
  deg_le_two : ∀ v, S v = true → cnt S (nbrs v) ≤ 2
  deg_pos : ∀ v, S v = true → 1 ≤ cnt S (nbrs v)
  /-- No set in which every vertex has two neighbours inside the set is fully selected:
  this covers 4-cycles, 6-cycles of 3-faces, and recorded cycle cuts. -/
  acyclic : ∀ C : List Nat, C ≠ [] →
    (∀ v ∈ C, 2 ≤ cnt (fun w => C.contains w) (nbrs v)) → ∃ v ∈ C, S v = false
  end_sel : ∀ v, E v = true → S v = true
  low_end : ∀ v, S v = true → cnt S (nbrs v) ≤ 1 → E v = true
  end_low : ∀ v, E v = true → cnt S (nbrs v) ≤ 1
  end_two : ∀ a b c, E a = true → E b = true → E c = true → a = b ∨ a = c ∨ b = c
  alpha : ∀ c ∈ centres,
    c.lo ≤ absentCorners S c.v c.d₁ c.d₂ ∧ absentCorners S c.v c.d₁ c.d₂ ≤ c.hi

/-! ## CNF semantics (DIMACS literals) -/

def litTrue (τ : Nat → Bool) (l : Int) : Bool :=
  if 0 < l then τ l.toNat else !τ (-l).toNat

def clauseTrue (τ : Nat → Bool) (c : List Int) : Bool := c.any (litTrue τ)

def cnfTrue (τ : Nat → Bool) (f : List (List Int)) : Bool := f.all (clauseTrue τ)

/-- Compact literal code used by generated data: `2*v` is `v`, `2*v+1` is `-v`. -/
def decodeLit (n : Nat) : Int := if n % 2 = 0 then Int.ofNat (n / 2) else -Int.ofNat (n / 2)

/-- No assignment satisfies every clause. -/
def Unsat (f : List (List Int)) : Prop := ∀ τ, cnfTrue τ f = false

/-! ## The 22 canonical windows behind the conditional bounds 242 and 241 -/

/-- Path directions of a canonical window `0 = x₀, x₁, …`. -/
def dirOfStep (u v : Nat) : Nat := Nat.log2 (u ^^^ v)

/-- Centres of a window with the given count bounds `(lo, hi)`. -/
def centresOf (window : List Nat) (bounds : List (Nat × Nat)) : List Centre :=
  (List.range bounds.length).map fun i =>
    let c := window.getD (i + 1) 0
    { v := c, d₁ := dirOfStep (window.getD i 0) c, d₂ := dirOfStep c (window.getD (i + 2) 0),
      lo := (bounds.getD i (0, 21)).1, hi := (bounds.getD i (0, 21)).2 }

/-- Triple shapes: directions `0,1,2,0` (repeated) and `0,1,2,3` (distinct). -/
def winRepeated : List Nat := [0, 1, 3, 7, 6]
def winDistinct : List Nat := [0, 1, 3, 7, 15]
/-- Quadruple shapes `0,1,2,0,3`, `0,1,2,3,0`, `0,1,2,3,4`. -/
def winQ01203 : List Nat := [0, 1, 3, 7, 6, 14]
def winQ01230 : List Nat := [0, 1, 3, 7, 15, 14]
def winQ01234 : List Nat := [0, 1, 3, 7, 15, 31]

/-- What a certificate module proves for one canonical window. -/
def Refuted (window : List Nat) (bounds : List (Nat × Nat)) : Prop :=
  ∀ S E : Nat → Bool, Axioms S E window (centresOf window bounds) → False

end Snake9.LocalWindow



/-! Variant of `LratCheck` with literal offset OFF = 5000 (up to 4999 variables), generated by
`milestones/23-k6-lean/scripts/gen_checker_variants_o5k.py`. -/


/-!
# A kernel-evaluable LRAT checker

Literals are bits of a `Nat`: variable `v < OFF` is bit `v`, its negation bit `v + OFF`,
where `OFF = 5000`.  In general bit `b` means `τ (b % OFF)` flipped `b / OFF` times
(`bitTrue`), so the negation of bit `b` is bit `b + OFF` or `b - OFF`.  A clause is the
`Nat` of its literals.

The clause database is a binary search tree keyed by slot numbers.  Proof data are
lists of `Nat`s, one per lemma, holding 13-bit words (lowest first):

  `slot  (lit+1) … (lit+1)  0  hint … hint  0`

(a hint is the slot of a database clause).  `check` runs reverse unit propagation for
each lemma; `replay` inserts the lemmas without checking anything.  Soundness:
`check t ps = true` and all clauses of `t` true imply all clauses of `replay t ps` true.

Every function evaluated by the kernel is written with recursors so that kernel
reduction does few unfoldings, and forces the database at each step so that no long
chains of suspended terms build up.
-/

namespace Snake9.LratO5k

open Snake9.LocalWindow

noncomputable section

/-- Kernel branch `if c then t else e`, written with `Bool.rec`. -/
local macro "kif " c:term " then " t:term " else " e:term : term =>
  `(Bool.rec (motive := fun _ => _) $e $t $c)

/-- Binary search tree `node key clause left right`. -/
inductive Tree where
  | nil : Tree
  | node (k c : Nat) (l r : Tree) : Tree

/-- Continue with the clause stored under key `k` (or with `dflt`). -/
def lookB (t : Tree) (k : Nat) (dflt : Bool) (f : Nat → Bool) : Bool :=
  Tree.rec (motive := fun _ => Bool) dflt
    (fun key c _ _ fl fr => kif k.blt key then fl else kif k.beq key then f c else fr) t

def lookT (t : Tree) (k : Nat) (dflt : Tree) (f : Nat → Tree) : Tree :=
  Tree.rec (motive := fun _ => Tree) dflt
    (fun key c _ _ fl fr => kif k.blt key then fl else kif k.beq key then f c else fr) t

/-- Evaluate `t` before continuing with `r`. -/
def seqT (t r : Tree) : Tree := Tree.rec (motive := fun _ => Tree) r (fun _ _ _ _ _ _ => r) t

/-- Store clause `c` under key `k`. -/
def setT (t : Tree) (k c : Nat) : Tree :=
  Tree.rec (motive := fun _ => Tree) (Tree.node k c .nil .nil)
    (fun key c' l r fl fr =>
      kif k.blt key then Tree.node key c' fl r else
      kif k.beq key then Tree.node key c l r else Tree.node key c' l fr) t

/-- `setT`, then evaluate the path to `k`. -/
def insertF (t : Tree) (k c : Nat) : Tree :=
  let t' := setT t k c
  lookT t' k t' (fun _ => t')

/-- Copies of `setT`/`insertF` used by `replay`, so that the trees of `replay` and of
`check` are different terms (the kernel caches compare equal-looking terms deeply). -/
def setT' (t : Tree) (k c : Nat) : Tree :=
  Tree.rec (motive := fun _ => Tree) (Tree.node k c .nil .nil)
    (fun key c' l r fl fr =>
      kif k.blt key then Tree.node key c' fl r else
      kif k.beq key then Tree.node key c l r else Tree.node key c' l fr) t

def insertF' (t : Tree) (k c : Nat) : Tree :=
  let t' := setT' t k c
  lookT t' k t' (fun _ => t')

/-! ## Lemmas -/

/-- Read the literal words of a lemma: returns the clause and the remaining words. -/
def litsL (fuel : Nat) : Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun c x => (c, x))
    (fun _ ih c x =>
      kif (x &&& 8191).beq 0 then (c, x >>> 13)
      else ih (c ||| (1 <<< ((x &&& 8191) - 1))) (x >>> 13)) fuel

def lemC (x : Nat) : Nat := (litsL 255 0 (x >>> 13)).1
def lemH (x : Nat) : Nat := (litsL 255 0 (x >>> 13)).2

/-- After looking up a hint clause: `u` are its literals not known to be false. -/
def hstep (ih : Nat → Nat → Bool) (z x u : Nat) : Bool :=
  kif u.beq 0 then true else
  kif (u &&& (u - 1)).beq 0 then
    ih (kif u.blt (2 ^ 5000) then z ||| (u <<< 5000) else z ||| (u >>> 5000)) x
  else ih z x

/-- Unit propagation over the hint words `x`; `z` holds the literals known false.
Returns `true` iff a conflict is reached.  The terminating word `0` is not a key, so
the lookup falls back to `false`. -/
def hints (db : Tree) (fuel : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih z x =>
      lookB db (x &&& 8191) false (fun d => hstep ih z (x >>> 13) (d ^^^ (d &&& z)))) fuel

def rup (t : Tree) (x : Nat) : Bool := hints t 4095 (lemC x) (lemH x)

def ins (t : Tree) (x : Nat) : Tree := insertF t (x &&& 8191) (lemC x)
def ins' (t : Tree) (x : Nat) : Tree := insertF' t (x &&& 8191) (lemC x)

def andB (a b : Bool) : Bool := kif a then b else false

def check (t : Tree) (ps : List Nat) : Bool :=
  List.rec (motive := fun _ => Tree → Bool) (fun _ => true)
    (fun x _ ih t => andB (rup t x) (ih (ins t x))) ps t

def replay (t : Tree) (ps : List Nat) : Tree :=
  List.rec (motive := fun _ => Tree → Tree) (fun t => t)
    (fun x _ ih t =>
      let t' := ins' t x
      seqT t' (ih t')) ps t

/-! ## Initial database and checkpoints -/

/-- The tautology `x₀ ∨ ¬x₀`, stored in slots without a clause. -/
def taut : Nat := 1 ||| (1 <<< 5000)

/-- Clause of `decodeLit` codes; a variable `≥ OFF` makes it the tautology. -/
def rawMask (c : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun k _ ih =>
      kif (k >>> 1).blt 5000 then
        (kif (k &&& 1).beq 0 then
          (kif k.beq 0 then ih ||| (1 <<< 5000) else ih ||| (1 <<< (k >>> 1)))
         else ih ||| (1 <<< ((k >>> 1) + 5000)))
      else ih ||| taut) c

/-- Insert tautologies under the given keys. -/
def shape (t : Tree) (keys : List Nat) : Tree :=
  List.rec (motive := fun _ => Tree → Tree) (fun t => t)
    (fun k _ ih t => let t' := insertF t k taut; seqT t' (ih t')) keys t

def loadRaw (t : Tree) (raw : List (List Nat)) (slots : List Nat) : Tree :=
  List.rec (motive := fun _ => Tree → List Nat → Tree) (fun t _ => t)
    (fun c _ ih t sl => List.rec (motive := fun _ => Tree) t
      (fun k rest _ => let t' := insertF t k (rawMask c); seqT t' (ih t' rest)) sl) raw t slots

/-- A checkpoint entry `key (lit+1) … (lit+1)` (no terminator needed). -/
def entC (x : Nat) : Nat := (litsL 255 0 (x >>> 13)).1

/-- Build a database from checkpoint entries. -/
def build (t : Tree) (es : List Nat) : Tree :=
  List.rec (motive := fun _ => Tree → Tree) (fun t => t)
    (fun x _ ih t => let t' := insertF t (x &&& 8191) (entC x); seqT t' (ih t')) es t

/-- Every checkpoint entry is in `t`. -/
def cpOk (t : Tree) (es : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => andB (lookB t (x &&& 8191) false (fun c => c.beq (entC x))) ih) es

/-- The empty clause is stored under key `k`. -/
def hasEmpty (t : Tree) (k : Nat) : Bool := lookB t k false (fun c => c.beq 0)

end

/-! ## Soundness -/

/-- Bit `b` is the literal `τ (b % 5000)`, negated if `b / 5000` is odd. -/
def bitTrue (τ : Nat → Bool) (b : Nat) : Bool := xor (τ (b % 5000)) ((b / 5000) % 2 == 1)

/-- Some literal of the clause `m` is true. -/
def MaskTrue (τ : Nat → Bool) (m : Nat) : Prop := ∃ b, m.testBit b = true ∧ bitTrue τ b = true

/-- All literals of `m` are false. -/
def AllFalse (τ : Nat → Bool) (m : Nat) : Prop := ∀ b, m.testBit b = true → bitTrue τ b = false

/-- All clauses of the tree are true.  (An inductive predicate, so that elaborating
`TreeTrue τ t` never evaluates `t`.) -/
inductive TreeTrue (τ : Nat → Bool) : Tree → Prop
  | nil : TreeTrue τ .nil
  | node {k c : Nat} {l r : Tree} : MaskTrue τ c → TreeTrue τ l → TreeTrue τ r →
      TreeTrue τ (.node k c l r)

theorem bitTrue_add (τ : Nat → Bool) (j : Nat) : bitTrue τ (j + 5000) = !bitTrue τ j := by
  unfold bitTrue
  have h1 : (j + 5000) % 5000 = j % 5000 := by omega
  have h2 : (j + 5000) / 5000 = j / 5000 + 1 := by omega
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one (j / 5000) with h | h
  · have : (j / 5000 + 1) % 2 = 1 := by omega
    rw [h, this]; cases τ (j % 5000) <;> rfl
  · have : (j / 5000 + 1) % 2 = 0 := by omega
    rw [h, this]; cases τ (j % 5000) <;> rfl

theorem bitTrue_sub (τ : Nat → Bool) (j : Nat) (hj : 5000 ≤ j) :
    bitTrue τ (j - 5000) = !bitTrue τ j := by
  have : j = (j - 5000) + 5000 := by omega
  conv => rhs; rw [this]
  rw [bitTrue_add, Bool.not_not]

theorem maskTrue_taut (τ : Nat → Bool) : MaskTrue τ taut := by
  cases h : τ 0
  · refine ⟨5000, ?_, ?_⟩
    · show (1 ||| (1 <<< 5000)).testBit 5000 = true
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]; simp
    · show xor (τ (5000 % 5000)) ((5000 / 5000) % 2 == 1) = true
      simp [h]
  · refine ⟨0, ?_, ?_⟩
    · show (1 ||| (1 <<< 5000)).testBit 0 = true
      rw [Nat.testBit_or]; simp
    · show xor (τ (0 % 5000)) ((0 / 5000) % 2 == 1) = true
      simp [h]

theorem maskTrue_or_left {τ : Nat → Bool} {a : Nat} (b : Nat) (h : MaskTrue τ a) :
    MaskTrue τ (a ||| b) := by
  obtain ⟨i, hi, ht⟩ := h
  exact ⟨i, by rw [Nat.testBit_or, hi]; rfl, ht⟩

theorem maskTrue_or_right {τ : Nat → Bool} (a : Nat) {b : Nat} (h : MaskTrue τ b) :
    MaskTrue τ (a ||| b) := by
  obtain ⟨i, hi, ht⟩ := h
  exact ⟨i, by rw [Nat.testBit_or, hi]; simp, ht⟩

theorem maskTrue_bit {τ : Nat → Bool} (i : Nat) (h : bitTrue τ i = true) : MaskTrue τ (1 <<< i) :=
  ⟨i, by rw [Nat.testBit_shiftLeft]; simp, h⟩

theorem not_maskTrue_zero (τ : Nat → Bool) : ¬ MaskTrue τ 0 := by
  rintro ⟨i, hi, _⟩; rw [Nat.zero_testBit] at hi; exact absurd hi (by decide)

/-! ### Trees -/

theorem lookB_spec {τ : Nat → Bool} (P : Bool → Prop) (k : Nat) (dflt : Bool) (f : Nat → Bool)
    (hd : P dflt) (hf : ∀ c, MaskTrue τ c → P (f c)) : ∀ t, TreeTrue τ t → P (lookB t k dflt f)
  | .nil, _ => hd
  | .node key c l r, .node hc hl hr => by
    show P (Bool.rec (Bool.rec (lookB r k dflt f) (f c) (k.beq key)) (lookB l k dflt f) (k.blt key))
    cases k.blt key
    · cases k.beq key
      · exact lookB_spec P k dflt f hd hf r hr
      · exact hf c hc
    · exact lookB_spec P k dflt f hd hf l hl

theorem lookT_const (k : Nat) (d : Tree) : ∀ t, lookT t k d (fun _ => d) = d
  | .nil => rfl
  | .node key c l r => by
    show Bool.rec (Bool.rec (lookT r k d (fun _ => d)) d (k.beq key)) (lookT l k d (fun _ => d))
      (k.blt key) = d
    rw [lookT_const k d l, lookT_const k d r]
    cases k.blt key <;> cases k.beq key <;> rfl

theorem setT_true {τ : Nat → Bool} (k c : Nat) (hc : MaskTrue τ c) :
    ∀ t, TreeTrue τ t → TreeTrue τ (setT t k c)
  | .nil, _ => .node hc .nil .nil
  | .node key c' l r, .node hc' hl hr => by
    show TreeTrue τ (Bool.rec (Bool.rec (Tree.node key c' l (setT r k c)) (Tree.node key c l r)
      (k.beq key)) (Tree.node key c' (setT l k c) r) (k.blt key))
    cases k.blt key
    · cases k.beq key
      · exact .node hc' hl (setT_true k c hc r hr)
      · exact .node hc hl hr
    · exact .node hc' (setT_true k c hc l hl) hr

theorem insertF_eq (t : Tree) (k c : Nat) : insertF t k c = setT t k c :=
  lookT_const k (setT t k c) (setT t k c)

theorem insertF'_eq (t : Tree) (k c : Nat) : insertF' t k c = setT t k c :=
  lookT_const k (setT' t k c) (setT' t k c)

theorem insertF_true {τ : Nat → Bool} {t : Tree} (k : Nat) {c : Nat} (ht : TreeTrue τ t)
    (hc : MaskTrue τ c) : TreeTrue τ (insertF t k c) := by
  rw [insertF_eq]; exact setT_true k c hc t ht

theorem seqT_eq (t r : Tree) : seqT t r = r := by cases t <;> rfl

/-! ### Unit propagation -/

theorem andB_eq_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

/-- A number whose bits are disjoint from those of its predecessor has at most one bit. -/
theorem single_bit : ∀ (u : Nat), (∀ i, (u.testBit i && (u - 1).testBit i) = false) →
    ∀ a b, u.testBit a = true → u.testBit b = true → a = b := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    intro hu a b ha hb
    rcases Nat.mod_two_eq_zero_or_one u with h | h
    · -- even: shift down
      have hu0 : u.testBit 0 = false := by rw [Nat.testBit_zero]; simp [h]
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := by
        cases a with
        | zero => rw [hu0] at ha; exact absurd ha (by decide)
        | succ a => exact ⟨a, rfl⟩
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := by
        cases b with
        | zero => rw [hu0] at hb; exact absurd hb (by decide)
        | succ b => exact ⟨b, rfl⟩
      have hpos : 0 < u := Nat.pos_of_ne_zero (by
        rintro rfl; rw [Nat.zero_testBit] at ha; exact absurd ha (by decide))
      have e1 : (u - 1) / 2 = u / 2 - 1 := by omega
      have hq : ∀ i, ((u / 2).testBit i && (u / 2 - 1).testBit i) = false := by
        intro i
        have := hu (i + 1)
        rw [Nat.testBit_succ, Nat.testBit_succ, e1] at this
        exact this
      rw [Nat.testBit_succ] at ha hb
      have := ih (u / 2) (by omega) hq a' b' ha hb
      omega
    · -- odd: no bit above 0
      have hz : ∀ i, u.testBit (i + 1) = false := by
        intro i
        have e1 : (u - 1) / 2 = u / 2 := by omega
        have := hu (i + 1)
        rw [Nat.testBit_succ, Nat.testBit_succ, e1, Bool.and_self] at this
        rw [Nat.testBit_succ]; exact this
      cases a with
      | succ a => rw [hz] at ha; exact absurd ha (by decide)
      | zero =>
        cases b with
        | succ b => rw [hz] at hb; exact absurd hb (by decide)
        | zero => rfl

theorem testBit_diff (d z i : Nat) :
    (d ^^^ (d &&& z)).testBit i = (d.testBit i && !z.testBit i) := by
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases d.testBit i <;> cases z.testBit i <;> rfl

theorem hstep_sound {τ : Nat → Bool} (ih : Nat → Nat → Bool)
    (hih : ∀ z x, AllFalse τ z → ih z x = true → False)
    (z x d : Nat) (hz : AllFalse τ z) (hd : MaskTrue τ d)
    (h : hstep ih z x (d ^^^ (d &&& z)) = true) : False := by
  obtain ⟨j, hdj, htj⟩ := hd
  -- the true literal `j` of `d` is not known false, so it is a bit of `u`
  have hzj : z.testBit j = false := by
    cases hzb : z.testBit j
    · rfl
    · have := hz j hzb; rw [htj] at this; exact absurd this (by decide)
  have huj : (d ^^^ (d &&& z)).testBit j = true := by rw [testBit_diff, hdj, hzj]; rfl
  revert h huj
  generalize d ^^^ (d &&& z) = u
  intro h huj
  have hst : hstep ih z x u = Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih z x)
        (ih (Bool.rec (motive := fun _ => Nat) (z ||| (u >>> 5000)) (z ||| (u <<< 5000))
          (u.blt (2 ^ 5000))) x) ((u &&& (u - 1)).beq 0)) true (u.beq 0) := rfl
  rw [hst] at h
  cases h0 : u.beq 0
  · rw [h0] at h
    cases h1 : (u &&& (u - 1)).beq 0
    · rw [h1] at h; exact hih z x hz h
    · rw [h1] at h
      have hsingle : ∀ i, u.testBit i = true → i = j := by
        intro i hi
        have hand : u &&& (u - 1) = 0 := Nat.eq_of_beq_eq_true h1
        exact single_bit u (fun k => by rw [← Nat.testBit_and, hand, Nat.zero_testBit]) i j hi huj
      cases h2 : u.blt (2 ^ 5000)
      · rw [h2] at h
        refine hih _ x ?_ h
        intro b hb
        rw [Nat.testBit_or] at hb
        rcases Bool.or_eq_true_iff.mp hb with hb | hb
        · exact hz b hb
        · rw [Nat.testBit_shiftRight] at hb
          have := hsingle _ hb
          have e : b = j - 5000 := by omega
          rw [e, bitTrue_sub τ j (by omega), htj]; rfl
      · rw [h2] at h
        refine hih _ x ?_ h
        intro b hb
        rw [Nat.testBit_or] at hb
        rcases Bool.or_eq_true_iff.mp hb with hb | hb
        · exact hz b hb
        · rw [Nat.testBit_shiftLeft, Bool.and_eq_true] at hb
          have hb1 : b ≥ 5000 := of_decide_eq_true hb.1
          have := hsingle _ hb.2
          have e : b = j + 5000 := by omega
          rw [e, bitTrue_add, htj]; rfl
  · -- conflict: every literal of `d` is known false
    have hu0 : u = 0 := Nat.eq_of_beq_eq_true h0
    rw [hu0, Nat.zero_testBit] at huj
    exact absurd huj (by decide)

theorem hints_sound {τ : Nat → Bool} {db : Tree} (hdb : TreeTrue τ db) :
    ∀ fuel z x, AllFalse τ z → hints db fuel z x = true → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro z x _ h
    rw [show hints db 0 z x = false from rfl] at h
    exact absurd h (by decide)
  | succ n ih =>
    intro z x hz h
    have key := lookB_spec (τ := τ) (fun b => AllFalse τ z → b = true → False) (x &&& 8191) false
      (fun d => hstep (hints db n) z (x >>> 13) (d ^^^ (d &&& z)))
      (fun _ h => absurd h (by decide))
      (fun c hc hz h => hstep_sound (hints db n) ih z (x >>> 13) c hz hc h) db hdb
    exact key hz h

theorem rup_sound {τ : Nat → Bool} {t : Tree} (ht : TreeTrue τ t) {x : Nat}
    (h : rup t x = true) : MaskTrue τ (lemC x) := by
  apply Classical.byContradiction
  intro hn
  have hz : AllFalse τ (lemC x) := by
    intro b hb
    cases hbt : bitTrue τ b
    · rfl
    · exact absurd ⟨b, hb, hbt⟩ hn
  exact hints_sound ht 4095 (lemC x) (lemH x) hz h

theorem replay_true (τ : Nat → Bool) {t : Tree} {ps : List Nat} (h : check t ps = true)
    (ht : TreeTrue τ t) : TreeTrue τ (replay t ps) := by
  induction ps generalizing t with
  | nil => exact ht
  | cons x xs ih =>
    have h' := andB_eq_true h
    have hins : TreeTrue τ (ins t x) := insertF_true _ ht (rup_sound ht h'.1)
    have e : replay t (x :: xs) = replay (ins t x) xs := by
      show seqT (ins' t x) (replay (ins' t x) xs) = _
      rw [seqT_eq]
      show replay (insertF' t (x &&& 8191) (lemC x)) xs = replay (insertF t (x &&& 8191) (lemC x)) xs
      rw [insertF_eq, insertF'_eq]
    rw [e]
    exact ih h'.2 hins

/-! ### Initial database, checkpoints, final conflict -/

theorem shape_true (τ : Nat → Bool) : ∀ (keys : List Nat) (t : Tree), TreeTrue τ t →
    TreeTrue τ (shape t keys)
  | [], _, ht => ht
  | k :: ks, t, ht => by
    show TreeTrue τ (seqT (insertF t k taut) (shape (insertF t k taut) ks))
    rw [seqT_eq]
    exact shape_true τ ks _ (insertF_true k ht (maskTrue_taut τ))

theorem decodeLit_even {k : Nat} (h : k % 2 = 0) : decodeLit k = ((k / 2 : Nat) : Int) := by
  unfold decodeLit; rw [if_pos h]; rfl

theorem decodeLit_odd {k : Nat} (h : k % 2 = 1) : decodeLit k = -((k / 2 : Nat) : Int) := by
  unfold decodeLit; rw [if_neg (by omega)]; rfl

theorem litTrue_ofNat (τ : Nat → Bool) (v : Nat) :
    litTrue τ (v : Int) = if v = 0 then !τ 0 else τ v := by
  unfold litTrue
  by_cases hv : v = 0
  · subst hv; simp
  · rw [if_pos (by omega), if_neg hv]; simp

theorem litTrue_negOfNat (τ : Nat → Bool) (v : Nat) : litTrue τ (-(v : Int)) = !τ v := by
  unfold litTrue; rw [if_neg (by omega)]; simp

theorem bitTrue_lt (τ : Nat → Bool) {v : Nat} (hv : v < 5000) : bitTrue τ v = τ v := by
  unfold bitTrue; rw [Nat.mod_eq_of_lt hv, Nat.div_eq_of_lt hv]; cases τ v <;> rfl

theorem rawMask_true (τ : Nat → Bool) : ∀ (c : List Nat),
    (c.map decodeLit).any (litTrue τ) = true → MaskTrue τ (rawMask c)
  | [], h => by simp at h
  | k :: ks, h => by
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true] at h
    have hs : k >>> 1 = k / 2 := by rw [Nat.shiftRight_eq_div_pow]
    have hand : k &&& 1 = k % 2 := Nat.and_one_is_mod k
    show MaskTrue τ (Bool.rec (motive := fun _ => Nat) (rawMask ks ||| taut)
      (Bool.rec (motive := fun _ => Nat) (rawMask ks ||| (1 <<< ((k >>> 1) + 5000)))
        (Bool.rec (motive := fun _ => Nat) (rawMask ks ||| (1 <<< (k >>> 1)))
          (rawMask ks ||| (1 <<< 5000)) (k.beq 0)) ((k &&& 1).beq 0)) ((k >>> 1).blt 5000))
    rw [hs, hand]
    rcases h with h | h
    · cases hb : (k / 2).blt 5000
      · exact maskTrue_or_right _ (maskTrue_taut τ)
      · have hk : k / 2 < 5000 := by rw [← Nat.blt_eq]; exact hb
        rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
        · rw [decodeLit_even h2, litTrue_ofNat] at h
          have e0 : (k % 2).beq 0 = true := by rw [h2]; rfl
          rw [e0]
          cases hk0 : k.beq 0
          · have hne : k / 2 ≠ 0 := by
              intro e
              have : k = 0 := by omega
              rw [this] at hk0; exact absurd hk0 (by decide)
            rw [if_neg hne] at h
            show MaskTrue τ (rawMask ks ||| (1 <<< (k / 2)))
            exact maskTrue_or_right _ (maskTrue_bit _ (by rw [bitTrue_lt τ hk]; exact h))
          · have e : k = 0 := Nat.eq_of_beq_eq_true hk0
            subst e
            simp at h
            show MaskTrue τ (rawMask ks ||| (1 <<< 5000))
            refine maskTrue_or_right _ (maskTrue_bit _ ?_)
            rw [show (5000 : Nat) = 0 + 5000 from rfl, bitTrue_add, bitTrue_lt τ (by decide), h]
            rfl
        · rw [decodeLit_odd h2, litTrue_negOfNat] at h
          have e0 : (k % 2).beq 0 = false := by rw [h2]; rfl
          rw [e0]
          show MaskTrue τ (rawMask ks ||| (1 <<< (k / 2 + 5000)))
          exact maskTrue_or_right _ (maskTrue_bit _ (by rw [bitTrue_add, bitTrue_lt τ hk]; exact h))
    · have hm := rawMask_true τ ks h
      cases (k / 2).blt 5000 <;> cases (k % 2).beq 0 <;> cases k.beq 0 <;>
        exact maskTrue_or_left _ hm

theorem loadRaw_true (τ : Nat → Bool) : ∀ (raw : List (List Nat)) (slots : List Nat) (t : Tree),
    (raw.map (·.map decodeLit)).all (clauseTrue τ) = true → TreeTrue τ t →
    TreeTrue τ (loadRaw t raw slots)
  | [], _, _, _, ht => ht
  | _ :: _, [], _, _, ht => ht
  | c :: cs, k :: ks, t, h, ht => by
    show TreeTrue τ (seqT (insertF t k (rawMask c)) (loadRaw (insertF t k (rawMask c)) cs ks))
    rw [seqT_eq]
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at h
    exact loadRaw_true τ cs ks _ h.2 (insertF_true k ht (rawMask_true τ c h.1))

theorem start_true (τ : Nat → Bool) {raw : List (List Nat)} {keys slots : List Nat}
    (h : cnfTrue τ (raw.map (·.map decodeLit)) = true) :
    TreeTrue τ (loadRaw (shape .nil keys) raw slots) :=
  loadRaw_true τ raw slots _ h (shape_true τ keys .nil .nil)

theorem build_true (τ : Nat → Bool) {R : Tree} (hR : TreeTrue τ R) :
    ∀ (es : List Nat) (t : Tree), cpOk R es = true → TreeTrue τ t → TreeTrue τ (build t es)
  | [], _, _, ht => ht
  | x :: xs, t, h, ht => by
    have h' := andB_eq_true h
    have hx : MaskTrue τ (entC x) :=
      lookB_spec (τ := τ) (fun b => b = true → MaskTrue τ (entC x)) (x &&& 8191) false
        (fun c => c.beq (entC x)) (fun h => absurd h (by decide))
        (fun c hc h => (Nat.eq_of_beq_eq_true h) ▸ hc) R hR h'.1
    show TreeTrue τ (seqT (insertF t (x &&& 8191) (entC x))
      (build (insertF t (x &&& 8191) (entC x)) xs))
    rw [seqT_eq]
    exact build_true τ hR xs _ h'.2 (insertF_true _ ht hx)

theorem cp_true (τ : Nat → Bool) {s : Tree} {ps cp keys : List Nat}
    (h : andB (check s ps) (cpOk (replay s ps) cp) = true) (hs : TreeTrue τ s) :
    TreeTrue τ (build (shape .nil keys) cp) :=
  build_true τ (replay_true τ (andB_eq_true h).1 hs) cp _ (andB_eq_true h).2
    (shape_true τ keys .nil .nil)

theorem final_false (τ : Nat → Bool) {s : Tree} {ps : List Nat} {k : Nat}
    (h : andB (check s ps) (hasEmpty (replay s ps) k) = true) (hs : TreeTrue τ s) : False :=
  lookB_spec (τ := τ) (fun b => b = true → False) k false (fun c => c.beq 0)
    (fun h => absurd h (by decide))
    (fun c hc h => not_maskTrue_zero τ ((Nat.eq_of_beq_eq_true h) ▸ hc))
    (replay s ps) (replay_true τ (andB_eq_true h).1 hs) (andB_eq_true h).2

theorem unsat_of_raw {raw : List (List Nat)}
    (h : ∀ τ, cnfTrue τ (raw.map (·.map decodeLit)) = true → False) :
    Unsat (raw.map (·.map decodeLit)) := by
  intro τ
  cases hc : cnfTrue τ (raw.map (·.map decodeLit))
  · rfl
  · exact absurd (h τ hc) id

end Snake9.LratO5k


/- UNCOMPILED generated adapter: source proof retained; W=18, OFF=5000, literal fuel=2048. -/

/-! Variant of `LratFast` with 18-bit words (clause keys up to 262143) and literal offset OFF = 5000 (up to 4999 variables), generated by
`milestones/23-k6-lean/scripts/gen_checker_variants_o5k.py`. -/


/-!
# A faster kernel-evaluable LRAT checker

The same proof format and soundness argument as `LratCheck` (whose trees, clause
semantics and lemmas are reused), with three changes that make kernel evaluation
several times faster:

* every operation evaluated by the kernel is a kernel-accelerated `Nat` primitive
  (`Nat.ble`, `Nat.beq`, `Nat.land`, `Nat.shiftRight`, …) applied directly, instead of
  `Nat.blt` or the `&&&`/`>>>`/`|||` notations, which the kernel unfolds through several
  definitions and instances at every use;
* the initial database shape is the perfect tree `perf h 0` with keys `1 … 2^h - 1` in
  order, built by one recursion instead of thousands of insertions;
* a checkpoint is a list of clauses in pre-order of `perf h 0` (the word `0` for an unused
  slot), built into a tree by one pass (`pre`); `cpOk` checks that each of its clauses is
  stored under the same key in the replayed database, so no property of `pre` is needed
  for soundness.  (Each tree clause is then a small closed term `entC x` with a literal
  `x`, which the kernel evaluates once and caches; a packed stream of entries, parsed with
  a running state, made every clause term depend on the whole stream and the checks about
  twice as slow.)

Proof data are lists of `Nat`s, one per lemma, holding 18-bit words (lowest first):

  `slot  (lit+1) … (lit+1)  0  hint … hint  0`

and a checkpoint entry is `(lit+1) … (lit+1)` (or `0`).
-/

namespace Snake9.PeerLratFast5000W18

open Snake9.LocalWindow
open Snake9.LratO5k (Tree TreeTrue MaskTrue AllFalse bitTrue taut rawMask andB)

noncomputable section

/-- Kernel branch `if c then t else e`, written with `Bool.rec`. -/
local macro "kif " c:term " then " t:term " else " e:term : term =>
  `(Bool.rec (motive := fun _ => _) $e $t $c)

/-- Continue with the clause stored under key `k` (or with `dflt`). -/
def lookB (t : Tree) (k : Nat) (dflt : Bool) (f : Nat → Bool) : Bool :=
  Tree.rec (motive := fun _ => Bool) dflt
    (fun key c _ _ fl fr => kif Nat.ble key k then (kif Nat.beq k key then f c else fr) else fl) t

def lookT (t : Tree) (k : Nat) (dflt : Tree) (f : Nat → Tree) : Tree :=
  Tree.rec (motive := fun _ => Tree) dflt
    (fun key c _ _ fl fr => kif Nat.ble key k then (kif Nat.beq k key then f c else fr) else fl) t

/-- Store clause `c` under key `k`. -/
def setT (t : Tree) (k c : Nat) : Tree :=
  Tree.rec (motive := fun _ => Tree) (Tree.node k c .nil .nil)
    (fun key c' l r fl fr =>
      kif Nat.ble key k then
        (kif Nat.beq k key then Tree.node key c l r else Tree.node key c' l fr)
      else Tree.node key c' fl r) t

/-- `setT`, then evaluate the path to `k`. -/
def insertF (t : Tree) (k c : Nat) : Tree :=
  let t' := setT t k c
  lookT t' k t' (fun _ => t')

/-- Copies of `setT`/`insertF` used by `replay`, so that the trees of `replay` and of
`check` are different terms. -/
def setT' (t : Tree) (k c : Nat) : Tree :=
  Tree.rec (motive := fun _ => Tree) (Tree.node k c .nil .nil)
    (fun key c' l r fl fr =>
      kif Nat.ble key k then
        (kif Nat.beq k key then Tree.node key c l r else Tree.node key c' l fr)
      else Tree.node key c' fl r) t

def insertF' (t : Tree) (k c : Nat) : Tree :=
  let t' := setT' t k c
  lookT t' k t' (fun _ => t')

/-! ## Lemmas -/

/-- Read the literal words of a lemma: returns the clause and the remaining words. -/
def litsL (fuel : Nat) : Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun c x => (c, x))
    (fun _ ih c x =>
      kif Nat.beq (Nat.land x 262143) 0 then (c, Nat.shiftRight x 18)
      else ih (Nat.lor c (Nat.shiftLeft 1 (Nat.sub (Nat.land x 262143) 1))) (Nat.shiftRight x 18))
    fuel

def lemC (x : Nat) : Nat := (litsL 2048 0 (Nat.shiftRight x 18)).1
def lemH (x : Nat) : Nat := (litsL 2048 0 (Nat.shiftRight x 18)).2

/-- `2 ^ 5000`: the negated literals are the bits from 5000 on. -/
@[irreducible] def big : Nat := Nat.pow 2 5000

/-- After looking up a hint clause: `u` are its literals not known to be false. -/
def hstep (ih : Nat → Nat → Bool) (z x u : Nat) : Bool :=
  kif Nat.beq u 0 then true else
  kif Nat.beq (Nat.land u (Nat.sub u 1)) 0 then
    ih (kif Nat.ble big u then Nat.lor z (Nat.shiftRight u 5000)
        else Nat.lor z (Nat.shiftLeft u 5000)) x
  else ih z x

/-- Unit propagation over the hint words `x`; `z` holds the literals known false.
Returns `true` iff a conflict is reached. -/
def hints (db : Tree) (fuel : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih z x =>
      lookB db (Nat.land x 262143) false
        (fun d => hstep ih z (Nat.shiftRight x 18) (Nat.xor d (Nat.land d z)))) fuel

def rup (t : Tree) (x : Nat) : Bool := hints t 4095 (lemC x) (lemH x)

def ins (t : Tree) (x : Nat) : Tree := insertF t (Nat.land x 262143) (lemC x)
def ins' (t : Tree) (x : Nat) : Tree := insertF' t (Nat.land x 262143) (lemC x)

def check (t : Tree) (ps : List Nat) : Bool :=
  List.rec (motive := fun _ => Tree → Bool) (fun _ => true)
    (fun x _ ih t => andB (rup t x) (ih (ins t x))) ps t

def replay (t : Tree) (ps : List Nat) : Tree :=
  List.rec (motive := fun _ => Tree → Tree) (fun t => t)
    (fun x _ ih t =>
      let t' := ins' t x
      LratO5k.seqT t' (ih t')) ps t

/-! ## Initial database and checkpoints -/

/-- The perfect tree of depth `d` with keys `b + 1 … b + 2^d - 1` in order, every clause
the tautology. -/
def perf (d : Nat) : Nat → Tree :=
  Nat.rec (motive := fun _ => Nat → Tree) (fun _ => Tree.nil)
    (fun d ih b => Tree.node (Nat.add b (Nat.pow 2 d)) taut (ih b) (ih (Nat.add b (Nat.pow 2 d)))) d

def loadRaw (t : Tree) (raw : List (List Nat)) (slots : List Nat) : Tree :=
  List.rec (motive := fun _ => Tree → List Nat → Tree) (fun t _ => t)
    (fun c _ ih t sl => List.rec (motive := fun _ => Tree) t
      (fun k rest _ => let t' := insertF t k (rawMask c); LratO5k.seqT t' (ih t' rest)) sl) raw t slots

/-- A checkpoint entry: its clause, or the tautology for `0`. -/
def entC (x : Nat) : Nat := kif Nat.beq x 0 then taut else (litsL 2048 0 x).1

/-- The tree of depth `d` (keys as in `perf d b`) whose clauses are the entries `es` in
pre-order; also returns the unused entries. -/
def pre (d : Nat) : Nat → List Nat → Tree × List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → Tree × List Nat) (fun _ es => (Tree.nil, es))
    (fun d ih b es => List.rec (motive := fun _ => Tree × List Nat) (Tree.nil, List.nil)
      (fun x rest _ =>
        let L := ih b rest
        let R := ih (Nat.add b (Nat.pow 2 d)) L.2
        (Tree.node (Nat.add b (Nat.pow 2 d)) (entC x) L.1 R.1, R.2)) es) d

/-- The database of a checkpoint. -/
def build (h : Nat) (es : List Nat) : Tree := (pre h 0 es).1

/-- Every clause of `t` is the tautology or stored under the same key in `R`. -/
def cpOk (R t : Tree) : Bool :=
  Tree.rec (motive := fun _ => Bool) true
    (fun k c _ _ fl fr =>
      andB (kif Nat.beq c taut then true else lookB R k false (fun d => Nat.beq d c))
        (andB fl fr)) t

/-- The empty clause is stored under key `k`. -/
def hasEmpty (t : Tree) (k : Nat) : Bool := lookB t k false (fun c => Nat.beq c 0)

end

/-! ## Soundness -/

open Snake9.LratO5k (maskTrue_taut not_maskTrue_zero single_bit testBit_diff bitTrue_add bitTrue_sub
  seqT seqT_eq andB_eq_true rawMask_true)

theorem lookB_spec {τ : Nat → Bool} (P : Bool → Prop) (k : Nat) (dflt : Bool) (f : Nat → Bool)
    (hd : P dflt) (hf : ∀ c, MaskTrue τ c → P (f c)) : ∀ t, TreeTrue τ t → P (lookB t k dflt f)
  | .nil, _ => hd
  | .node key c l r, .node hc hl hr => by
    show P (Bool.rec (lookB l k dflt f) (Bool.rec (lookB r k dflt f) (f c) (Nat.beq k key))
      (Nat.ble key k))
    cases Nat.ble key k
    · exact lookB_spec P k dflt f hd hf l hl
    · cases Nat.beq k key
      · exact lookB_spec P k dflt f hd hf r hr
      · exact hf c hc

theorem lookT_const (k : Nat) (d : Tree) : ∀ t, lookT t k d (fun _ => d) = d
  | .nil => rfl
  | .node key c l r => by
    show Bool.rec (lookT l k d (fun _ => d)) (Bool.rec (lookT r k d (fun _ => d)) d (Nat.beq k key))
      (Nat.ble key k) = d
    rw [lookT_const k d l, lookT_const k d r]
    cases Nat.ble key k <;> cases Nat.beq k key <;> rfl

theorem setT_true {τ : Nat → Bool} (k c : Nat) (hc : MaskTrue τ c) :
    ∀ t, TreeTrue τ t → TreeTrue τ (setT t k c)
  | .nil, _ => .node hc .nil .nil
  | .node key c' l r, .node hc' hl hr => by
    show TreeTrue τ (Bool.rec (Tree.node key c' (setT l k c) r)
      (Bool.rec (Tree.node key c' l (setT r k c)) (Tree.node key c l r) (Nat.beq k key))
      (Nat.ble key k))
    cases Nat.ble key k
    · exact .node hc' (setT_true k c hc l hl) hr
    · cases Nat.beq k key
      · exact .node hc' hl (setT_true k c hc r hr)
      · exact .node hc hl hr

theorem setT'_eq (t : Tree) (k c : Nat) : setT' t k c = setT t k c := rfl

theorem insertF_eq (t : Tree) (k c : Nat) : insertF t k c = setT t k c :=
  lookT_const k (setT t k c) (setT t k c)

theorem insertF'_eq (t : Tree) (k c : Nat) : insertF' t k c = setT t k c :=
  lookT_const k (setT' t k c) (setT' t k c)

theorem insertF_true {τ : Nat → Bool} {t : Tree} (k : Nat) {c : Nat} (ht : TreeTrue τ t)
    (hc : MaskTrue τ c) : TreeTrue τ (insertF t k c) := by
  rw [insertF_eq]; exact setT_true k c hc t ht

theorem hstep_sound {τ : Nat → Bool} (ih : Nat → Nat → Bool)
    (hih : ∀ z x, AllFalse τ z → ih z x = true → False)
    (z x d : Nat) (hz : AllFalse τ z) (hd : MaskTrue τ d)
    (h : hstep ih z x (Nat.xor d (Nat.land d z)) = true) : False := by
  obtain ⟨j, hdj, htj⟩ := hd
  have hzj : z.testBit j = false := by
    cases hzb : z.testBit j
    · rfl
    · have := hz j hzb; rw [htj] at this; exact absurd this (by decide)
  have huj : (Nat.xor d (Nat.land d z)).testBit j = true := by
    show (d ^^^ (d &&& z)).testBit j = true
    rw [testBit_diff, hdj, hzj]; rfl
  revert h huj
  generalize Nat.xor d (Nat.land d z) = u
  intro h huj
  have hst : hstep ih z x u = Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih z x)
        (ih (Bool.rec (motive := fun _ => Nat) (z ||| (u <<< 5000)) (z ||| (u >>> 5000))
          (Nat.ble big u)) x) ((u &&& (u - 1)).beq 0)) true (u.beq 0) := rfl
  rw [hst] at h
  cases h0 : u.beq 0
  · rw [h0] at h
    cases h1 : (u &&& (u - 1)).beq 0
    · rw [h1] at h; exact hih z x hz h
    · rw [h1] at h
      have hsingle : ∀ i, u.testBit i = true → i = j := by
        intro i hi
        have hand : u &&& (u - 1) = 0 := Nat.eq_of_beq_eq_true h1
        exact single_bit u (fun k => by rw [← Nat.testBit_and, hand, Nat.zero_testBit]) i j hi huj
      cases h2 : Nat.ble big u
      · rw [h2] at h
        refine hih _ x ?_ h
        intro b hb
        rw [Nat.testBit_or] at hb
        rcases Bool.or_eq_true_iff.mp hb with hb | hb
        · exact hz b hb
        · rw [Nat.testBit_shiftLeft, Bool.and_eq_true] at hb
          have hb1 : b ≥ 5000 := of_decide_eq_true hb.1
          have := hsingle _ hb.2
          have e : b = j + 5000 := by omega
          rw [e, bitTrue_add, htj]; rfl
      · rw [h2] at h
        refine hih _ x ?_ h
        intro b hb
        rw [Nat.testBit_or] at hb
        rcases Bool.or_eq_true_iff.mp hb with hb | hb
        · exact hz b hb
        · rw [Nat.testBit_shiftRight] at hb
          have := hsingle _ hb
          have e : b = j - 5000 := by omega
          rw [e, bitTrue_sub τ j (by omega), htj]; rfl
  · have hu0 : u = 0 := Nat.eq_of_beq_eq_true h0
    rw [hu0, Nat.zero_testBit] at huj
    exact absurd huj (by decide)

theorem hints_sound {τ : Nat → Bool} {db : Tree} (hdb : TreeTrue τ db) :
    ∀ fuel z x, AllFalse τ z → hints db fuel z x = true → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro z x _ h
    rw [show hints db 0 z x = false from rfl] at h
    exact absurd h (by decide)
  | succ n ih =>
    intro z x hz h
    have key := lookB_spec (τ := τ) (fun b => AllFalse τ z → b = true → False) (Nat.land x 262143)
      false (fun d => hstep (hints db n) z (Nat.shiftRight x 18) (Nat.xor d (Nat.land d z)))
      (fun _ h => absurd h (by decide))
      (fun c hc hz h => hstep_sound (hints db n) ih z (Nat.shiftRight x 18) c hz hc h) db hdb
    exact key hz h

theorem rup_sound {τ : Nat → Bool} {t : Tree} (ht : TreeTrue τ t) {x : Nat}
    (h : rup t x = true) : MaskTrue τ (lemC x) := by
  apply Classical.byContradiction
  intro hn
  have hz : AllFalse τ (lemC x) := by
    intro b hb
    cases hbt : bitTrue τ b
    · rfl
    · exact absurd ⟨b, hb, hbt⟩ hn
  exact hints_sound ht 4095 (lemC x) (lemH x) hz h

theorem replay_true (τ : Nat → Bool) {t : Tree} {ps : List Nat} (h : check t ps = true)
    (ht : TreeTrue τ t) : TreeTrue τ (replay t ps) := by
  induction ps generalizing t with
  | nil => exact ht
  | cons x xs ih =>
    have h' := andB_eq_true h
    have hins : TreeTrue τ (ins t x) := insertF_true _ ht (rup_sound ht h'.1)
    have e : replay t (x :: xs) = replay (ins t x) xs := by
      show seqT (ins' t x) (replay (ins' t x) xs) = _
      rw [seqT_eq]
      show replay (insertF' t (Nat.land x 262143) (lemC x)) xs
        = replay (insertF t (Nat.land x 262143) (lemC x)) xs
      rw [insertF_eq, insertF'_eq]
    rw [e]
    exact ih h'.2 hins

/-! ### Initial database, checkpoints, final conflict -/

theorem perf_true (τ : Nat → Bool) : ∀ d b, TreeTrue τ (perf d b)
  | 0, _ => .nil
  | d + 1, b => .node (maskTrue_taut τ) (perf_true τ d b) (perf_true τ d _)

theorem loadRaw_true (τ : Nat → Bool) : ∀ (raw : List (List Nat)) (slots : List Nat) (t : Tree),
    (raw.map (·.map decodeLit)).all (clauseTrue τ) = true → TreeTrue τ t →
    TreeTrue τ (loadRaw t raw slots)
  | [], _, _, _, ht => ht
  | _ :: _, [], _, _, ht => ht
  | c :: cs, k :: ks, t, h, ht => by
    show TreeTrue τ (seqT (insertF t k (rawMask c)) (loadRaw (insertF t k (rawMask c)) cs ks))
    rw [seqT_eq]
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at h
    exact loadRaw_true τ cs ks _ h.2 (insertF_true k ht (rawMask_true τ c h.1))

theorem start_true (τ : Nat → Bool) {raw : List (List Nat)} {h : Nat} {slots : List Nat}
    (hr : cnfTrue τ (raw.map (·.map decodeLit)) = true) :
    TreeTrue τ (loadRaw (perf h 0) raw slots) :=
  loadRaw_true τ raw slots _ hr (perf_true τ h 0)

theorem cpOk_true (τ : Nat → Bool) {R : Tree} (hR : TreeTrue τ R) :
    ∀ t, cpOk R t = true → TreeTrue τ t
  | .nil, _ => .nil
  | .node k c l r, h => by
    have h' := andB_eq_true h
    have h'' := andB_eq_true h'.2
    refine .node ?_ (cpOk_true τ hR l h''.1) (cpOk_true τ hR r h''.2)
    have hc := h'.1
    revert hc
    show Bool.rec (lookB R k false (fun d => Nat.beq d c)) true (Nat.beq c taut) = true →
      MaskTrue τ c
    cases hct : Nat.beq c taut
    · exact lookB_spec (τ := τ) (fun b => b = true → MaskTrue τ c) k false
        (fun d => Nat.beq d c) (fun h => absurd h (by decide))
        (fun d hd h => (Nat.eq_of_beq_eq_true h) ▸ hd) R hR
    · intro _
      exact (Nat.eq_of_beq_eq_true hct) ▸ maskTrue_taut τ

theorem cp_true (τ : Nat → Bool) {s : Tree} {ps : List Nat} {t : Tree}
    (h : andB (check s ps) (cpOk (replay s ps) t) = true) (hs : TreeTrue τ s) : TreeTrue τ t :=
  cpOk_true τ (replay_true τ (andB_eq_true h).1 hs) t (andB_eq_true h).2

theorem final_false (τ : Nat → Bool) {s : Tree} {ps : List Nat} {k : Nat}
    (h : andB (check s ps) (hasEmpty (replay s ps) k) = true) (hs : TreeTrue τ s) : False :=
  lookB_spec (τ := τ) (fun b => b = true → False) k false (fun c => Nat.beq c 0)
    (fun h => absurd h (by decide))
    (fun c hc h => not_maskTrue_zero τ ((Nat.eq_of_beq_eq_true h) ▸ hc))
    (replay s ps) (replay_true τ (andB_eq_true h).1 hs) (andB_eq_true h).2

end Snake9.PeerLratFast5000W18


/- UNCOMPILED generated adapter: source proof retained; W=18, OFF=5000, literal fuel=2048. -/

/-! Variant of `LratFast2` with 18-bit words (clause keys up to 262143) and literal offset OFF = 5000 (up to 4999 variables), generated by
`milestones/23-k6-lean/scripts/gen_checker_variants_o5k.py`. -/


/-!
# LRAT checking with a cached start database

`LratFast` looks up every hint clause in the current database, a binary tree of depth
up to 15 that changes after every lemma, so every lookup walks the tree again.  But most
hints of a segment (about 94% on the 238 windows) name clauses that were already in the
database when the segment started, and few distinct ones (about 5% as many keys as hints).

`check2 S D ps` keeps the start database `S` fixed and inserts the lemmas of the
segment into a second tree `D`.  A hint word with the flag bit `131072` set names a key of
`S`, otherwise a key of `D`.  A lookup in `S` is written as the term
`Nat.add 0 (lookC S (Nat.succ m))` with a literal `m`, through a `Nat.rec` on the key:
the kernel evaluates this term once per key and then finds it in its cache, so repeated
hints on the same start clause cost a cache hit instead of a tree walk.

Soundness needs no relation between the flags and the proof: every clause of `S` and of
`D` is true, so whichever tree a hint is looked up in, the looked-up clause is true.
The database of the next segment is still `replay S ps` (`LratFast.replay`).

Proof words are those of `LratFast` (`slot lits 0 hints 0`); keys must be below `131072`.
-/

namespace Snake9.PeerLratFast2_5000W18

open Snake9.LocalWindow
open Snake9.LratO5k (Tree TreeTrue MaskTrue AllFalse taut andB)
open Snake9.PeerLratFast5000W18 (lookB insertF hstep lemC lemH ins replay perf cpOk hasEmpty)

noncomputable section

/-- Kernel branch `if c then t else e`, written with `Bool.rec`. -/
local macro "kif " c:term " then " t:term " else " e:term : term =>
  `(Bool.rec (motive := fun _ => _) $e $t $c)

/-- The clause stored under key `k` (the tautology if there is none). -/
def lookC (t : Tree) (k : Nat) : Nat :=
  Tree.rec (motive := fun _ => Nat) taut
    (fun key c _ _ fl fr => kif Nat.ble key k then (kif Nat.beq k key then c else fr) else fl) t

/-- `lookC s k`, reached through a term that depends only on `s` and the value of `k`,
which the kernel caches. -/
def getS (s : Tree) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) taut (fun m _ => Nat.add 0 (lookC s (Nat.succ m))) k

/-- Unit propagation over the hint words `x`, looking up flagged hints in `S` and the
others in `D`. -/
def hints2 (S D : Tree) (fuel : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih z x =>
      kif Nat.ble 131072 (Nat.land x 262143) then
        hstep ih z (Nat.shiftRight x 18)
          (Nat.xor (getS S (Nat.sub (Nat.land x 262143) 131072))
            (Nat.land (getS S (Nat.sub (Nat.land x 262143) 131072)) z))
      else lookB D (Nat.land x 262143) false
        (fun d => hstep ih z (Nat.shiftRight x 18) (Nat.xor d (Nat.land d z)))) fuel

def rup2 (S D : Tree) (x : Nat) : Bool := hints2 S D 4095 (lemC x) (lemH x)

/-- Check the lemmas `ps` against the start database `S` and the tree `D` of the lemmas
checked so far. -/
def check2 (S : Tree) : Tree → List Nat → Bool := fun D ps =>
  List.rec (motive := fun _ => Tree → Bool) (fun _ => true)
    (fun x _ ih D => andB (rup2 S D x) (ih (ins D x))) ps D

/-- Every clause of `t` is the tautology or equal to the clause at the same position of
`R` (the two trees are walked together; checkpoints and replayed databases have the same
perfect shape).  `cpOk` instead looks every clause up by key. -/
def cpZ (R t : Tree) : Bool :=
  Tree.rec (motive := fun _ => Tree → Bool) (fun _ => true)
    (fun _ c _ _ fl fr R => Tree.rec (motive := fun _ => Bool) false
      (fun _ c' l' r' _ _ => andB (kif Nat.beq c taut then true else Nat.beq c' c)
        (andB (fl l') (fr r'))) R) t R

end

/-! ## Soundness -/

open Snake9.LratO5k (maskTrue_taut seqT seqT_eq andB_eq_true)
open Snake9.PeerLratFast5000W18 (lookB_spec hstep_sound insertF_true insertF_eq insertF'_eq perf_true
  cpOk_true)

theorem lookC_true {τ : Nat → Bool} (k : Nat) : ∀ t, TreeTrue τ t → MaskTrue τ (lookC t k)
  | .nil, _ => maskTrue_taut τ
  | .node key c l r, .node hc hl hr => by
    show MaskTrue τ (Bool.rec (lookC l k) (Bool.rec (lookC r k) c (Nat.beq k key)) (Nat.ble key k))
    cases Nat.ble key k
    · exact lookC_true k l hl
    · cases Nat.beq k key
      · exact lookC_true k r hr
      · exact hc

theorem getS_true {τ : Nat → Bool} {t : Tree} (ht : TreeTrue τ t) : ∀ k, MaskTrue τ (getS t k)
  | 0 => maskTrue_taut τ
  | m + 1 => by
    show MaskTrue τ (Nat.add 0 (lookC t (Nat.succ m)))
    rw [show Nat.add 0 (lookC t (Nat.succ m)) = lookC t (Nat.succ m) from Nat.zero_add _]
    exact lookC_true _ t ht

theorem hints2_sound {τ : Nat → Bool} {S D : Tree} (hS : TreeTrue τ S) (hD : TreeTrue τ D) :
    ∀ fuel z x, AllFalse τ z → hints2 S D fuel z x = true → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro z x _ h
    rw [show hints2 S D 0 z x = false from rfl] at h
    exact absurd h (by decide)
  | succ n ih =>
    intro z x hz h
    revert h
    show Bool.rec (motive := fun _ => Bool)
        (lookB D (Nat.land x 262143) false
          (fun d => hstep (hints2 S D n) z (Nat.shiftRight x 18) (Nat.xor d (Nat.land d z))))
        (hstep (hints2 S D n) z (Nat.shiftRight x 18)
          (Nat.xor (getS S (Nat.sub (Nat.land x 262143) 131072))
            (Nat.land (getS S (Nat.sub (Nat.land x 262143) 131072)) z)))
        (Nat.ble 131072 (Nat.land x 262143)) = true → False
    cases Nat.ble 131072 (Nat.land x 262143)
    · exact lookB_spec (τ := τ) (fun b => b = true → False) (Nat.land x 262143) false
        (fun d => hstep (hints2 S D n) z (Nat.shiftRight x 18) (Nat.xor d (Nat.land d z)))
        (fun h => absurd h (by decide))
        (fun c hc h => hstep_sound (hints2 S D n) ih z (Nat.shiftRight x 18) c hz hc h) D hD
    · exact hstep_sound (hints2 S D n) ih z (Nat.shiftRight x 18) _ hz (getS_true hS _)

theorem rup2_sound {τ : Nat → Bool} {S D : Tree} (hS : TreeTrue τ S) (hD : TreeTrue τ D)
    {x : Nat} (h : rup2 S D x = true) : MaskTrue τ (lemC x) := by
  apply Classical.byContradiction
  intro hn
  have hz : AllFalse τ (lemC x) := by
    intro b hb
    cases hbt : Snake9.LratO5k.bitTrue τ b
    · rfl
    · exact absurd ⟨b, hb, hbt⟩ hn
  exact hints2_sound hS hD 4095 (lemC x) (lemH x) hz h

/-- The replayed database stays true when `check2` accepts the lemmas. -/
theorem replay_true2' (τ : Nat → Bool) {S : Tree} (hS : TreeTrue τ S) :
    ∀ (ps : List Nat) (D t : Tree), check2 S D ps = true → TreeTrue τ D → TreeTrue τ t →
      TreeTrue τ (replay t ps)
  | [], _, _, _, _, ht => ht
  | x :: xs, D, t, h, hD, ht => by
    have h' := andB_eq_true h
    have hx := rup2_sound hS hD h'.1
    have e : replay t (x :: xs) = replay (ins t x) xs := by
      show seqT (Snake9.PeerLratFast5000W18.ins' t x) (replay (Snake9.PeerLratFast5000W18.ins' t x) xs) = _
      rw [seqT_eq]
      show replay (Snake9.PeerLratFast5000W18.insertF' t (Nat.land x 262143) (lemC x)) xs
        = replay (insertF t (Nat.land x 262143) (lemC x)) xs
      rw [insertF_eq, insertF'_eq]
    rw [e]
    exact replay_true2' τ hS xs (ins D x) (ins t x) h'.2 (insertF_true _ hD hx)
      (insertF_true _ ht hx)

theorem replay_true2 (τ : Nat → Bool) {t : Tree} {ps : List Nat} {h : Nat}
    (hc : check2 t (perf h 0) ps = true) (ht : TreeTrue τ t) : TreeTrue τ (replay t ps) :=
  replay_true2' τ ht ps _ t hc (perf_true τ h 0) ht

theorem cp_true2 (τ : Nat → Bool) {s : Tree} {ps : List Nat} {t : Tree} {h : Nat}
    (hc : andB (check2 s (perf h 0) ps) (cpOk (replay s ps) t) = true) (hs : TreeTrue τ s) :
    TreeTrue τ t :=
  cpOk_true τ (replay_true2 τ (andB_eq_true hc).1 hs) t (andB_eq_true hc).2

theorem cpZ_true (τ : Nat → Bool) : ∀ t R, TreeTrue τ R → cpZ R t = true → TreeTrue τ t
  | .nil, _, _, _ => .nil
  | .node _ c l r, .nil, _, h => absurd h (by
      show ¬ (false = true)
      decide)
  | .node k c l r, .node k' c' l' r', .node hc' hl' hr', h => by
    have h' := andB_eq_true h
    have h'' := andB_eq_true h'.2
    refine .node ?_ (cpZ_true τ l l' hl' h''.1) (cpZ_true τ r r' hr' h''.2)
    have hc := h'.1
    revert hc
    show Bool.rec (Nat.beq c' c) true (Nat.beq c taut) = true → MaskTrue τ c
    cases hct : Nat.beq c taut
    · intro h; exact (Nat.eq_of_beq_eq_true h) ▸ hc'
    · intro _; exact (Nat.eq_of_beq_eq_true hct) ▸ maskTrue_taut τ

theorem cpz_true2 (τ : Nat → Bool) {s : Tree} {ps : List Nat} {t : Tree} {h : Nat}
    (hc : andB (check2 s (perf h 0) ps) (cpZ (replay s ps) t) = true) (hs : TreeTrue τ s) :
    TreeTrue τ t :=
  cpZ_true τ t _ (replay_true2 τ (andB_eq_true hc).1 hs) (andB_eq_true hc).2

theorem final_false2 (τ : Nat → Bool) {s : Tree} {ps : List Nat} {k h : Nat}
    (hc : andB (check2 s (perf h 0) ps) (hasEmpty (replay s ps) k) = true) (hs : TreeTrue τ s) :
    False :=
  lookB_spec (τ := τ) (fun b => b = true → False) k false (fun c => Nat.beq c 0)
    (fun h => absurd h (by decide))
    (fun c hc h => Snake9.LratO5k.not_maskTrue_zero τ ((Nat.eq_of_beq_eq_true h) ▸ hc))
    (replay s ps) (replay_true2 τ (andB_eq_true hc).1 hs) (andB_eq_true hc).2

end Snake9.PeerLratFast2_5000W18


set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PeerLratSmoke
open Snake9.LocalWindow
open Snake9.LratO5k (Tree TreeTrue andB unsat_of_raw)
open Snake9.PeerLratFast5000W18
open Snake9.PeerLratFast2_5000W18
def raw : List (List Nat) := [[2], [3]]
def cnf := raw.map (List.map decodeLit)
noncomputable def start : Tree := loadRaw (perf 2 0) raw [1,2]
noncomputable def proof : List Nat := [nat_lit 2361228277499815788547]
theorem checked : andB (check2 start (perf 2 0) proof) (hasEmpty (replay start proof) 3) = true := by
  decide +kernel
theorem unsat : Unsat cnf := by
  apply unsat_of_raw
  intro t h
  have hs : TreeTrue t start := start_true (raw := raw) (h := 2) (slots := [1,2]) t h
  exact final_false2 (s := start) (ps := proof) (h := 2) t checked hs
#print axioms checked
#print axioms unsat
end PeerLratSmoke


namespace PeerLratFormatControls
open Snake9.LocalWindow
open Snake9.LratO5k (Tree TreeTrue andB unsat_of_raw)
open Snake9.PeerLratFast5000W18
open Snake9.PeerLratFast2_5000W18


namespace Variable4007
def raw : List (List Nat) := [[8014], [8015]]
def cnf := raw.map (List.map decodeLit)
noncomputable def start : Tree := loadRaw (perf 2 0) raw [1, 2]
noncomputable def proof : List Nat := [nat_lit 2361228277499815788547]
theorem checked : andB (check2 start (perf 2 0) proof) (hasEmpty (replay start proof) 3) = true := by decide +kernel
theorem unsat : Unsat cnf := by
  apply unsat_of_raw
  intro t ht
  have hs : TreeTrue t start := start_true (raw := raw) (h := 2) (slots := [1, 2]) t ht
  exact final_false2 (s := start) (ps := proof) (h := 2) t checked hs
#print axioms checked
#print axioms unsat
end Variable4007


namespace ClauseID70000
def raw : List (List Nat) := [[2], [3]]
def cnf := raw.map (List.map decodeLit)
noncomputable def start : Tree := loadRaw (perf 17 0) raw [70000, 70001]
noncomputable def proof : List Nat := [nat_lit 3622222969059697299826]
theorem checked : andB (check2 start (perf 17 0) proof) (hasEmpty (replay start proof) 70002) = true := by decide +kernel
theorem unsat : Unsat cnf := by
  apply unsat_of_raw
  intro t ht
  have hs : TreeTrue t start := start_true (raw := raw) (h := 17) (slots := [70000, 70001]) t ht
  exact final_false2 (s := start) (ps := proof) (h := 17) t checked hs
#print axioms checked
#print axioms unsat
end ClauseID70000


namespace LearnedClause300
def raw : List (List Nat) := [[2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132, 134, 136, 138, 140, 142, 144, 146, 148, 150, 152, 154, 156, 158, 160, 162, 164, 166, 168, 170, 172, 174, 176, 178, 180, 182, 184, 186, 188, 190, 192, 194, 196, 198, 200, 202, 204, 206, 208, 210, 212, 214, 216, 218, 220, 222, 224, 226, 228, 230, 232, 234, 236, 238, 240, 242, 244, 246, 248, 250, 252, 254, 256, 258, 260, 262, 264, 266, 268, 270, 272, 274, 276, 278, 280, 282, 284, 286, 288, 290, 292, 294, 296, 298, 300, 302, 304, 306, 308, 310, 312, 314, 316, 318, 320, 322, 324, 326, 328, 330, 332, 334, 336, 338, 340, 342, 344, 346, 348, 350, 352, 354, 356, 358, 360, 362, 364, 366, 368, 370, 372, 374, 376, 378, 380, 382, 384, 386, 388, 390, 392, 394, 396, 398, 400, 402, 404, 406, 408, 410, 412, 414, 416, 418, 420, 422, 424, 426, 428, 430, 432, 434, 436, 438, 440, 442, 444, 446, 448, 450, 452, 454, 456, 458, 460, 462, 464, 466, 468, 470, 472, 474, 476, 478, 480, 482, 484, 486, 488, 490, 492, 494, 496, 498, 500, 502, 504, 506, 508, 510, 512, 514, 516, 518, 520, 522, 524, 526, 528, 530, 532, 534, 536, 538, 540, 542, 544, 546, 548, 550, 552, 554, 556, 558, 560, 562, 564, 566, 568, 570, 572, 574, 576, 578, 580, 582, 584, 586, 588, 590, 592, 594, 596, 598, 600], [3], [5], [7], [9], [11], [13], [15], [17], [19], [21], [23], [25], [27], [29], [31], [33], [35], [37], [39], [41], [43], [45], [47], [49], [51], [53], [55], [57], [59], [61], [63], [65], [67], [69], [71], [73], [75], [77], [79], [81], [83], [85], [87], [89], [91], [93], [95], [97], [99], [101], [103], [105], [107], [109], [111], [113], [115], [117], [119], [121], [123], [125], [127], [129], [131], [133], [135], [137], [139], [141], [143], [145], [147], [149], [151], [153], [155], [157], [159], [161], [163], [165], [167], [169], [171], [173], [175], [177], [179], [181], [183], [185], [187], [189], [191], [193], [195], [197], [199], [201], [203], [205], [207], [209], [211], [213], [215], [217], [219], [221], [223], [225], [227], [229], [231], [233], [235], [237], [239], [241], [243], [245], [247], [249], [251], [253], [255], [257], [259], [261], [263], [265], [267], [269], [271], [273], [275], [277], [279], [281], [283], [285], [287], [289], [291], [293], [295], [297], [299], [301], [303], [305], [307], [309], [311], [313], [315], [317], [319], [321], [323], [325], [327], [329], [331], [333], [335], [337], [339], [341], [343], [345], [347], [349], [351], [353], [355], [357], [359], [361], [363], [365], [367], [369], [371], [373], [375], [377], [379], [381], [383], [385], [387], [389], [391], [393], [395], [397], [399], [401], [403], [405], [407], [409], [411], [413], [415], [417], [419], [421], [423], [425], [427], [429], [431], [433], [435], [437], [439], [441], [443], [445], [447], [449], [451], [453], [455], [457], [459], [461], [463], [465], [467], [469], [471], [473], [475], [477], [479], [481], [483], [485], [487], [489], [491], [493], [495], [497], [499], [501], [503], [505], [507], [509], [511], [513], [515], [517], [519], [521], [523], [525], [527], [529], [531], [533], [535], [537], [539], [541], [543], [545], [547], [549], [551], [553], [555], [557], [559], [561], [563], [565], [567], [569], [571], [573], [575], [577], [579], [581], [583], [585], [587], [589], [591], [593], [595], [597], [599], [601]]
def cnf := raw.map (List.map decodeLit)
noncomputable def start : Tree := loadRaw (perf 9 0) raw [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301]
noncomputable def proof : List Nat := [nat_lit 3285259418748558788940240620462819060297919324370907330178621468724006191152350102555616723929817208307508072897395668427537129772224697764771453353140915427698387740022643266613685397989783398373828846058970589439682216812541680746697247100548683647829843532976540805727633100207006314990113227462152397154920693265241469604247586445294203366970980655704907137917078150057702320139526019063377033164033839952259730330853505319166686567356653277129054001436771422466762868547752902954106843277423609641262861361621330047343552427294704006556580496409231050184653894792025345431248622089518207219233383982517481604739525317144362838441301327067866064625849021633280947057656400530642388042740070002416238019983620446312465235039217551177261321158378028481828401060275210539523888937843975988165022618707480810344487478530450056811485049806172503150576702120746894615534290314933921453371550598180894158780486490309979212508699116548266639171304577467147445422117509082023080449760421066792052372740362385382329334450871660043717471405361346604281686096823934899456822285803251654518602471693908516958044073490614807528541416060408101642032694132719500584395559824362371017085164306895547572748174184134992073349500263069162367831531550018437320767494593776838451405411622913152591782294883710682646477454610649439994118025646283097139576866886059825179407381987296612381529619399996422209291693580293345543592297167358508014947909686386853502132075733608152410943251329302558764979649646935943266162258539079795991673427968901066189392422097790599998392997673095678480056908481112067615636076281955546748621385789868960993545219489753035440430, nat_lit 7581994405142275521698238140742110657549754463849552163204990283287973754065683550657361334234444088339773864814296800885250608870050946092642480256131704260897371596735951207923497817693075254883351083388455347087281232420506572989195046185137010606945401486402540080810316732792541277605045761588205329045854840906078693021088277605976484960661004354961581823903989320061337772855436839266559575843548670666910980426773366338760809687549162398128003600508866268340308281602558801150397350337035247471675566555073120528170718013717661967416583265873048372280446034529422450731813637957338994185945678498175057117439642600779101150154923516882443975800427068546141218840918222464047588776916461183748390203544970978761495873713926805847776434544560192535501467504425310514371177270757922508125692647141419941879339484941026055975318152065427181845188406667021048268676813677256733715372718375248061087573178989482466469521036055802664173132324630485533363642777902436667876587139906470959305887936986412219944377513845586175430300576666203631398239447829945983295271062843530636632648266461731421505668964822789601212587258411502504321619808921768057953498636563943416154631956697330460134336680737337287643039707079927743113151491190951841344072135650477591948519871252670530500406928357073246522941979218728392631614272895085253162159455272616171749591790665731509660038195005533175921711976714494109082520273468423997820531558028345624729057667562595246126024122839898553696437059009964252954779052482197335534975730839887041236376599305739188972184320692693006921594715253953079726502676427115786156838193486011372172943586548485456175]
theorem checked : andB (check2 start (perf 9 0) proof) (hasEmpty (replay start proof) 303) = true := by decide +kernel
theorem unsat : Unsat cnf := by
  apply unsat_of_raw
  intro t ht
  have hs : TreeTrue t start := start_true (raw := raw) (h := 9) (slots := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301]) t ht
  exact final_false2 (s := start) (ps := proof) (h := 9) t checked hs
#print axioms checked
#print axioms unsat
end LearnedClause300


namespace RejectControls
def raw : List (List Nat) := [[2],[4]]
def cnf := raw.map (List.map decodeLit)
noncomputable def start : Tree := loadRaw (perf 2 0) raw [1,2]
noncomputable def falseProof : List Nat := [nat_lit 2361228277499815788547]
noncomputable def malformedProof : List Nat := [nat_lit 9075850012000259]
theorem false_unsat_rejected : check2 start (perf 2 0) falseProof = false := by decide +kernel
theorem missing_hint_rejected : check2 start (perf 2 0) malformedProof = false := by decide +kernel
theorem actual_sat_assignment : cnfTrue (fun _ => true) cnf = true := by decide +kernel
theorem not_unsat : Not (Unsat cnf) := by
  intro h
  have bad : (true : Bool) = false := actual_sat_assignment.symm.trans (h (fun _ => true))
  cases bad
#print axioms false_unsat_rejected
#print axioms missing_hint_rejected
#print axioms actual_sat_assignment
#print axioms not_unsat
end RejectControls
end PeerLratFormatControls
