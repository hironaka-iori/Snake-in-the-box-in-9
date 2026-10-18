import TwoMissingPairs
import NormalizeAdjacentSingletons
import WindowCornerData

namespace Snake9.WindowSingletons
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Coordinate pairs not using either of the two prescribed path directions. -/
def eligiblePairs (a b : Coord) : Finset AxisPair :=
  Finset.univ.filter (fun cd => cd.val.1 ≠ a ∧ cd.val.1 ≠ b ∧ cd.val.2 ≠ a ∧ cd.val.2 ≠ b)

/-- Missing opposite corners among the eligible pairs at a specified center. -/
def missingCorners {m : Nat} (p : Snake m) (v : Vertex) (a b : Coord) : Finset AxisPair :=
  (eligiblePairs a b).filter (fun cd => ¬ InPath p (vxor v (pair cd.val.1 cd.val.2)))

theorem missingCorners_zero {m : Nat} (p : Snake m) (a b : Coord)
    (h0 : InPath p 0) (ha : InPath p (unit a)) (hb : InPath p (unit b)) (hab : a ≠ b) :
    missingCorners p 0 a b = missingAxisPairs p := by
  have hu (c : Coord) : InPath p (unit c) ↔ c = a ∨ c = b := by
    constructor
    · exact unit_cover_two p a b h0 ha hb hab c
    · rintro (rfl | rfl)
      · exact ha
      · exact hb
  ext cd
  simp only [missingCorners,eligiblePairs,missingAxisPairs,Finset.mem_filter,Finset.mem_univ,
    true_and,vxor_zero_left,singleton_at_zero_iff,hu,h0,not_or,true_and]
  tauto

/-- The encoding's missing-corner count is exactly the established singleton
count, at any center with two distinct prescribed selected neighbors. -/
theorem missingCorners_card {m : Nat} (p : Snake m) (i : Fin (m+1)) (v : Vertex)
    (hiv : p.vertex i = v) (a b : Coord) (hab : a ≠ b)
    (ha : InPath p (vxor v (unit a))) (hb : InPath p (vxor v (unit b))) :
    (missingCorners p v a b).card = localAlpha p i := by
  let q := translate p v
  have hqi : q.vertex i = 0 := by
    change vxor v (p.vertex i) = 0
    rw [hiv,vxor_self]
  have hqa : InPath q (unit a) := (inPath_translate_at p v (unit a)).mpr ha
  have hqb : InPath q (unit b) := (inPath_translate_at p v (unit b)).mpr hb
  have he : missingCorners p v a b = missingCorners q 0 a b := by
    ext cd
    simp only [missingCorners,Finset.mem_filter,vxor_zero_left]
    rw [show InPath q (pair cd.val.1 cd.val.2) ↔ InPath p (vxor v (pair cd.val.1 cd.val.2)) from inPath_translate_at p v _]
  rw [he,missingCorners_zero q a b ⟨i,hqi⟩ hqa hqb hab]
  exact (missingAxisPairs_card q i hqi).trans (localAlpha_translate p v i)

/-- Typed coordinate pairs in the same increasing order as the explicit encoding. -/
def encodedPairs (a b : Coord) : List AxisPair :=
  ((List.finRange 9).flatMap (fun c => (List.finRange 9).filterMap (fun d =>
    if h : c.val < d.val then some (⟨(c,d),h⟩ : AxisPair) else none))).filter
      (fun cd => decide (cd.val.1 ≠ a ∧ cd.val.1 ≠ b ∧ cd.val.2 ≠ a ∧ cd.val.2 ≠ b))

theorem encoded_pairs_checked : ∀ a b : Coord,
    (encodedPairs a b).Nodup ∧ (encodedPairs a b).toFinset = eligiblePairs a b := by decide

def pairMissingCount {m : Nat} (p : Snake m) (v : Vertex) (xs : List AxisPair) : Nat :=
  xs.countP (fun cd => decide (¬ InPath p (vxor v (pair cd.val.1 cd.val.2))))

theorem pairMissingCount_eq_card {m : Nat} (p : Snake m) (v : Vertex) (a b : Coord)
    (xs : List AxisPair) (hn : xs.Nodup) (he : xs.toFinset = eligiblePairs a b) :
    pairMissingCount p v xs = (missingCorners p v a b).card := by
  have h := List.toFinset_card_of_nodup
    (hn.filter (fun cd => decide (¬ InPath p (vxor v (pair cd.val.1 cd.val.2)))))
  simpa [pairMissingCount,List.countP_eq_length_filter,List.toFinset_filter,he,missingCorners]
    using h.symm

def selectedNat {m : Nat} (p : Snake m) (n : Nat) : Bool :=
  decide (InPath p (⟨n % 512,Nat.mod_lt _ (by decide)⟩ : Vertex))

def CornerAgreement (v : Vertex) (a b : Coord) : Prop :=
  ((encodedPairs a b).map (fun cd => (vxor v (pair cd.val.1 cd.val.2)).val)) =
    WindowCornerData.corners v.val a.val b.val

theorem corner_agreements : CornerAgreement 1 0 1 ∧ CornerAgreement 3 1 2 ∧
    CornerAgreement 7 2 0 ∧ CornerAgreement 7 2 3 := by
  unfold CornerAgreement
  decide

/-- The actual snake's selection indicators give the exact count used by the encoding. -/
theorem encoded_missing_count {m : Nat} (p : Snake m) (i : Fin (m+1)) (v : Vertex)
    (hiv : p.vertex i = v) (a b : Coord) (hab : a ≠ b)
    (ha : InPath p (vxor v (unit a))) (hb : InPath p (vxor v (unit b)))
    (hcode : CornerAgreement v a b) :
    WindowCornerData.missingCount (selectedNat p)
      (WindowCornerData.corners v.val a.val b.val) = localAlpha p i := by
  rw [← hcode]
  have hcount : WindowCornerData.missingCount (selectedNat p)
      ((encodedPairs a b).map (fun cd => (vxor v (pair cd.val.1 cd.val.2)).val)) =
      pairMissingCount p v (encodedPairs a b) := by
    simp [WindowCornerData.missingCount,pairMissingCount,List.countP_map,Function.comp_def,selectedNat,
      Nat.mod_eq_of_lt (vxor v (pair _ _)).isLt]
  rw [hcount,pairMissingCount_eq_card p v a b _ (encoded_pairs_checked a b).1
    (encoded_pairs_checked a b).2]
  exact missingCorners_card p i v hiv a b hab ha hb

/-- Every actual singleton count supplies a satisfying assignment to its complete counter. -/
theorem encoded_counter_exists {m : Nat} (p : Snake m) (i : Fin (m+1)) (v : Vertex)
    (hiv : p.vertex i = v) (a b : Coord) (hab : a ≠ b)
    (ha : InPath p (vxor v (unit a))) (hb : InPath p (vxor v (unit b)))
    (hcode : CornerAgreement v a b) (k : Nat) (hk : localAlpha p i = k) :
    ∃ s, WindowCornerData.MissingCounterSystem (selectedNat p)
      (WindowCornerData.corners v.val a.val b.val) k s := by
  apply (WindowCornerData.missing_counter_iff _ _ _).mpr
  exact (encoded_missing_count p i v hiv a b hab ha hb hcode).trans hk

#print axioms missingCorners_zero
#print axioms missingCorners_card
#print axioms encoded_pairs_checked
#print axioms corner_agreements
#print axioms encoded_missing_count
#print axioms encoded_counter_exists
end
end Snake9.WindowSingletons
