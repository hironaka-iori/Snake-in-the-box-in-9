import LocalWindowModel

/-!
# The local share model: window certificates with a corner-share cap

Stage 1 of `milestones/11-local-ceiling/s0_lean_design.md` (§2.1).  A share
certificate refutes, on the radius-four ball of a canonical window, the local window
axioms `Axioms` together with a cap on the window's corner share

  `shareSum M S centres = Σ_{c ∈ centres} shareLocal M S c.v`,

where `shareLocal M S x = Σ_{k < 9} ⌊M · e0(x ⊕ e_k) / d(x ⊕ e_k)⌋` mirrors the global
`shareN` of `work/spectral/ShareCharge.lean`: `e0(q) = emptyCount S q` is the number of
the 36 squares at `q` with no selected corner, and `d(q) = cnt S (nbrs q)` the number
of selected neighbours of `q` (`Nat.div` gives `0` when `d(q) = 0`; a selected `q` has
`e0(q) = 0`, so the two path neighbours of a centre contribute nothing).

`Refuted W b` implies `RefutedShare W b M K` for every `K` (`refutedShare_of_refuted`),
so the existing exclusion certificates stay valid as share certificates with any cap.
-/

namespace Snake9.LocalWindow

/-- The square at `q` spanned by the coordinates `ab` has no selected corner. -/
def emptyPred (S : Nat → Bool) (q : Nat) (ab : Nat × Nat) : Bool :=
  !S q && !S (q ^^^ (1 <<< ab.1)) && !S (q ^^^ (1 <<< ab.2)) &&
  !S (q ^^^ (1 <<< ab.1) ^^^ (1 <<< ab.2))

/-- `e0(q)`: empty squares at `q` over all 36 coordinate pairs (mirrors `emptyAt`). -/
def emptyCount (S : Nat → Bool) (q : Nat) : Nat :=
  ((freePairs 9 9).filter (emptyPred S q)).length

/-- `shareN_M(x)` over the nine neighbours of `x` (mirrors `shareN`). -/
def shareLocal (M : Nat) (S : Nat → Bool) (x : Nat) : Nat :=
  ((List.range 9).map fun k =>
    M * emptyCount S (x ^^^ (1 <<< k)) / cnt S (nbrs (x ^^^ (1 <<< k)))).sum

/-- The share sum of a list of window centres. -/
def shareSum (M : Nat) (S : Nat → Bool) (cs : List Centre) : Nat :=
  (cs.map fun c => shareLocal M S c.v).sum

/-- `Axioms` plus a cap on the window's share sum.  A share certificate refutes the cap. -/
structure AxiomsS (S E : Nat → Bool) (window : List Nat) (centres : List Centre)
    (M cap : Nat) : Prop extends Axioms S E window centres where
  share_le : shareSum M S centres ≤ cap

/-- What a share certificate module proves for one canonical window: no normalized
snake vertex set around the window has share sum at most `cap`. -/
def RefutedShare (window : List Nat) (bounds : List (Nat × Nat)) (M cap : Nat) : Prop :=
  ∀ S E : Nat → Bool, AxiomsS S E window (centresOf window bounds) M cap → False

/-! ## Elementary facts -/

theorem AxiomsS.mono {S E : Nat → Bool} {window : List Nat} {centres : List Centre}
    {M cap cap' : Nat} (h : AxiomsS S E window centres M cap) (hc : cap ≤ cap') :
    AxiomsS S E window centres M cap' :=
  ⟨h.toAxioms, Nat.le_trans h.share_le hc⟩

/-- A refuted cap refutes every smaller cap. -/
theorem RefutedShare.anti {window : List Nat} {bounds : List (Nat × Nat)} {M cap cap' : Nat}
    (h : RefutedShare window bounds M cap) (hc : cap' ≤ cap) :
    RefutedShare window bounds M cap' :=
  fun S E ax => h S E (ax.mono hc)

/-- A plain exclusion certificate is a share certificate for every cap. -/
theorem refutedShare_of_refuted {window : List Nat} {bounds : List (Nat × Nat)}
    (h : Refuted window bounds) (M cap : Nat) : RefutedShare window bounds M cap :=
  fun S E ax => h S E ax.toAxioms

/-- `emptyPred` with the two coordinates swapped. -/
theorem emptyPred_symm (S : Nat → Bool) (q a b : Nat) :
    emptyPred S q (b, a) = emptyPred S q (a, b) := by
  unfold emptyPred
  simp only
  rw [Nat.xor_assoc q (1 <<< b), Nat.xor_comm (1 <<< b), ← Nat.xor_assoc]
  cases S q <;> cases S (q ^^^ (1 <<< a)) <;> cases S (q ^^^ (1 <<< b)) <;> simp

theorem emptyPred_sort (S : Nat → Bool) (q x y : Nat) :
    emptyPred S q (min x y, max x y) = emptyPred S q (x, y) := by
  by_cases h : x ≤ y
  · rw [Nat.min_eq_left h, Nat.max_eq_right h]
  · rw [Nat.min_eq_right (by omega), Nat.max_eq_left (by omega), emptyPred_symm]

/-- The characterisation used by the identification with `emptyAt` (all four corners
unselected, written with `2 ^ a`). -/
theorem emptyPred_iff (S : Nat → Bool) (q a b : Nat) :
    emptyPred S q (a, b) = true ↔
      S q = false ∧ S (q ^^^ 2 ^ a) = false ∧ S (q ^^^ 2 ^ b) = false ∧
        S (q ^^^ 2 ^ a ^^^ 2 ^ b) = false := by
  unfold emptyPred
  simp only [Nat.one_shiftLeft, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- A selected vertex has no empty square (mirrors `emptyAt_eq_zero_of_inPath`). -/
theorem emptyCount_eq_zero_of_sel (S : Nat → Bool) {q : Nat} (hq : S q = true) :
    emptyCount S q = 0 := by
  unfold emptyCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro ab _
  unfold emptyPred
  rw [hq]
  simp

/-- The selected-neighbour count as a count over the nine coordinates (the shape the
identification with `selDeg` consumes). -/
theorem cnt_nbrs_eq (S : Nat → Bool) (v : Nat) :
    cnt S (nbrs v) = ((List.range 9).filter fun k => S (v ^^^ 2 ^ k)).length := by
  unfold cnt nbrs
  rw [List.filter_map, List.length_map]
  rfl

/-- `shareLocal` written with `2 ^ k`. -/
theorem shareLocal_eq (M : Nat) (S : Nat → Bool) (x : Nat) :
    shareLocal M S x = ((List.range 9).map fun k =>
      M * emptyCount S (x ^^^ 2 ^ k) / cnt S (nbrs (x ^^^ 2 ^ k))).sum := by
  unfold shareLocal
  simp only [Nat.one_shiftLeft]

end Snake9.LocalWindow
