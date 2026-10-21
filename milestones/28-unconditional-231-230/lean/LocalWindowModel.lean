import Std

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
