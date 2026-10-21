import LocalWindowShareModel

/-! Core, executable definitions of the parallel-square share (weights 6/3/2).
These are distinct from the existing corner-share definitions. -/
namespace Snake9.LocalWindow

def selectedBit (b : Bool) : Nat := if b then 1 else 0

def parallelCount (S : Nat → Bool) (v : Nat) (ab : Nat × Nat) : Nat :=
  selectedBit (S v) + selectedBit (S (v ^^^ 2 ^ ab.1)) +
    selectedBit (S (v ^^^ 2 ^ ab.2)) + selectedBit (S (v ^^^ 2 ^ ab.1 ^^^ 2 ^ ab.2))

def parallelWeight (n : Nat) : Nat :=
  if n = 1 then 6 else if n = 2 then 3 else if n = 3 then 2 else 0

def parallelTerm (S : Nat → Bool) (v k : Nat) (ab : Nat × Nat) : Nat :=
  if k ≠ ab.1 ∧ k ≠ ab.2 ∧ emptyPred S (v ^^^ 2 ^ k) ab = true
  then parallelWeight (parallelCount S v ab) else 0

def parallelShare (S : Nat → Bool) (v : Nat) : Nat :=
  ((List.range 9).map fun k =>
    ((freePairs 9 9).map fun ab => parallelTerm S v k ab).sum).sum

def parallelSum (S : Nat → Bool) (cs : List Centre) : Nat :=
  (cs.map fun c => parallelShare S c.v).sum

structure AxiomsP (S E : Nat → Bool) (window : List Nat) (centres : List Centre)
    (cap : Nat) : Prop extends Axioms S E window centres where
  share_le : parallelSum S centres ≤ cap

def RefutedParallel (window : List Nat) (bounds : List (Nat × Nat)) (cap : Nat) : Prop :=
  ∀ S E : Nat → Bool, AxiomsP S E window (centresOf window bounds) cap → False

theorem AxiomsP.mono {S E : Nat → Bool} {window : List Nat} {centres : List Centre}
    {cap cap' : Nat} (h : AxiomsP S E window centres cap) (hc : cap ≤ cap') :
    AxiomsP S E window centres cap' := ⟨h.toAxioms, Nat.le_trans h.share_le hc⟩

theorem parallelCount_symm (S : Nat → Bool) (v a b : Nat) :
    parallelCount S v (b, a) = parallelCount S v (a, b) := by
  unfold parallelCount
  simp only
  rw [Nat.xor_assoc v (2 ^ b), Nat.xor_comm (2 ^ b), ← Nat.xor_assoc]
  omega

theorem parallelTerm_symm (S : Nat → Bool) (v k a b : Nat) :
    parallelTerm S v k (b, a) = parallelTerm S v k (a, b) := by
  unfold parallelTerm
  rw [emptyPred_symm, parallelCount_symm]
  simp only
  have : (k ≠ b ∧ k ≠ a ∧ emptyPred S (v ^^^ 2 ^ k) (a, b) = true) ↔
      (k ≠ a ∧ k ≠ b ∧ emptyPred S (v ^^^ 2 ^ k) (a, b) = true) := by
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2, h1, h3⟩
  simp only [this]

theorem parallelTerm_sort (S : Nat → Bool) (v k a b : Nat) :
    parallelTerm S v k (min a b, max a b) = parallelTerm S v k (a, b) := by
  by_cases h : a ≤ b
  · rw [Nat.min_eq_left h, Nat.max_eq_right h]
  · rw [Nat.min_eq_right (by omega), Nat.max_eq_left (by omega), parallelTerm_symm]

theorem parallelTerm_zero_of_neighbor (S : Nat → Bool) (v k : Nat) (ab : Nat × Nat)
    (hs : S (v ^^^ 2 ^ k) = true) : parallelTerm S v k ab = 0 := by
  simp [parallelTerm, emptyPred, hs]

#print axioms parallelTerm_symm
#print axioms parallelTerm_zero_of_neighbor
end Snake9.LocalWindow
