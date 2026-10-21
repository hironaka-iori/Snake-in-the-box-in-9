import ParallelShareModel
import ParallelShareTerm
import LocalWindowBridge

/-! Geometric premises needed for the unary encoding of one parallel share. -/
namespace Snake9.LocalWindow
set_option maxHeartbeats 1000000

def squareVertices (v a b : Nat) : List Nat :=
  [v, v ^^^ 2 ^ a, v ^^^ 2 ^ b, v ^^^ 2 ^ a ^^^ 2 ^ b]

theorem xor_swap (v a b : Nat) : v ^^^ a ^^^ b = v ^^^ b ^^^ a := by
  rw [Nat.xor_assoc, Nat.xor_comm a b, ← Nat.xor_assoc]

theorem square_flip1 (v a b w : Nat) (h : w ∈ squareVertices v a b) :
    w ^^^ 2 ^ a ∈ squareVertices v a b := by
  simp only [squareVertices, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (xor_aa _ _)
  · exact Or.inr (Or.inr (Or.inr (xor_swap _ _ _)))
  · exact Or.inr (Or.inr (Or.inl (xor_aba _ _ _)))

theorem square_flip2 (v a b w : Nat) (h : w ∈ squareVertices v a b) :
    w ^^^ 2 ^ b ∈ squareVertices v a b := by
  simp only [squareVertices, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inl (xor_aa _ _)
  · exact Or.inr (Or.inl (xor_aa _ _))

theorem square_two_neighbors (v a b w : Nat) (ha : a < 9) (hb : b < 9)
    (hab : a ≠ b) (hw : w ∈ squareVertices v a b) :
    2 ≤ cnt (fun u => (squareVertices v a b).contains u) (nbrs w) := by
  unfold cnt
  apply two_le_length_of_mem (a := w ^^^ 2 ^ a) (b := w ^^^ 2 ^ b)
  · rw [List.mem_filter, List.contains_iff_mem]
    exact ⟨mem_nbrs _ _ |>.2 ⟨a, ha, rfl⟩, square_flip1 v a b w hw⟩
  · rw [List.mem_filter, List.contains_iff_mem]
    exact ⟨mem_nbrs _ _ |>.2 ⟨b, hb, rfl⟩, square_flip2 v a b w hw⟩
  · intro h
    exact hab (pow_two_inj (xor_left_inj w h))

theorem Axioms.square_missing {S E : Nat → Bool} {W : List Nat} {cs : List Centre}
    (ax : Axioms S E W cs) (v a b : Nat) (ha : a < 9) (hb : b < 9) (hab : a ≠ b) :
    ∃ w ∈ squareVertices v a b, S w = false := by
  apply ax.acyclic (squareVertices v a b) (by simp [squareVertices])
  intro w hw
  exact square_two_neighbors v a b w ha hb hab hw

theorem Axioms.parallelCount_le_three {S E : Nat → Bool} {W : List Nat} {cs : List Centre}
    (ax : Axioms S E W cs) (v a b : Nat) (ha : a < 9) (hb : b < 9) (hab : a ≠ b) :
    parallelCount S v (a, b) ≤ 3 := by
  obtain ⟨w, hw, hs⟩ := ax.square_missing v a b ha hb hab
  simp only [squareVertices, List.mem_cons, List.not_mem_nil, or_false] at hw
  unfold parallelCount selectedBit
  rcases hw with rfl | rfl | rfl | rfl <;> simp only [hs, Bool.false_eq_true, ↓reduceIte]
  all_goals split <;> split <;> split <;> omega

open Snake9.ParallelShareTerm

/-- A selected centre has at most two other selected corners in its square. -/
theorem Axioms.other_corners_le_two {S E : Nat → Bool} {W : List Nat} {cs : List Centre}
    (ax : Axioms S E W cs) (v a b : Nat) (ha : a < 9) (hb : b < 9) (hab : a ≠ b)
    (hv : S v = true) :
    others (S (v ^^^ 2 ^ a)) (S (v ^^^ 2 ^ b)) (S (v ^^^ 2 ^ a ^^^ 2 ^ b)) ≤ 2 := by
  have h := ax.parallelCount_le_three v a b ha hb hab
  simp only [parallelCount, selectedBit, hv, ↓reduceIte] at h
  unfold others bit
  omega

theorem parallelWeight_div {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 3) :
    parallelWeight n = 6 / n := by
  have h : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases h with rfl | rfl | rfl <;> decide

/-- The actual geometric share term equals the weight of the encoder's six
unary bits. The missing-square premise is proved from acyclicity, not assumed. -/
theorem Axioms.parallel_unary_weight {S E : Nat → Bool} {W : List Nat} {cs : List Centre}
    (ax : Axioms S E W cs) (v k a b : Nat) (ha : a < 9) (hb : b < 9) (hab : a ≠ b)
    (hv : S v = true) (hka : k ≠ a) (hkb : k ≠ b) :
    let e := emptyPred S (v ^^^ 2 ^ k) (a, b)
    let x := S (v ^^^ 2 ^ a)
    let y := S (v ^^^ 2 ^ b)
    let z := S (v ^^^ 2 ^ a ^^^ 2 ^ b)
    parallelTerm S v k (a, b) = 2 * bit e + bit (gate1 e x y z) + 3 * bit (gate3 e x y z) := by
  dsimp only
  have ho := ax.other_corners_le_two v a b ha hb hab hv
  have hc : parallelCount S v (a, b) =
      1 + others (S (v ^^^ 2 ^ a)) (S (v ^^^ 2 ^ b)) (S (v ^^^ 2 ^ a ^^^ 2 ^ b)) := by
    simp only [parallelCount, selectedBit, hv, ↓reduceIte, others, bit]
    omega
  have hw := parallelWeight_div (n := 1 + others (S (v ^^^ 2 ^ a))
    (S (v ^^^ 2 ^ b)) (S (v ^^^ 2 ^ a ^^^ 2 ^ b))) (by omega) (by omega)
  have hu := (unary_weight (emptyPred S (v ^^^ 2 ^ k) (a, b)) _ _ _ ho).symm
  unfold parallelTerm
  by_cases he : emptyPred S (v ^^^ 2 ^ k) (a, b) = true
  · rw [if_pos ⟨hka, hkb, he⟩, hc, hw]
    simpa only [he, ↓reduceIte] using hu
  · rw [if_neg (fun h => he h.2.2)]
    simpa only [he, ↓reduceIte] using hu

#print axioms Axioms.parallelCount_le_three
#print axioms Axioms.other_corners_le_two
#print axioms Axioms.parallel_unary_weight
end Snake9.LocalWindow
