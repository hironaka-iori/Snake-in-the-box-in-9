import AggregateSingletonBound
import WindowGeometry

namespace Snake9.Window244
open SquareIncidence Finset
open scoped BigOperators
noncomputable section
local instance propDecAlpha (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0

/-- The two window neighbours exhaust a selected centre's available degree. -/
theorem other_coordinate_absent {m : Nat} (p : Snake m) (v : Vertex)
    (a b c : Coord) (hv : InPath p v)
    (ha : InPath p (flip a v)) (hb : InPath p (flip b v))
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    ¬ InPath p (flip c v) := by
  intro hc
  rcases selected_three_neighbors_repeat p hv ha hb hc
    (flip_adj a v) (flip_adj b v) (flip_adj c v) with h | h | h
  · exact hab (flip_inj_coord v h)
  · exact hca (flip_inj_coord v h).symm
  · exact hcb (flip_inj_coord v h).symm

/-- A square through a saturated centre is singleton exactly when it avoids
the two path directions and its opposite corner is absent. -/
theorem singleton_eligible {m : Nat} (p : Snake m) (v : Vertex)
    (a b : Coord) (hv : InPath p v)
    (ha : InPath p (flip a v)) (hb : InPath p (flip b v)) (hab : a ≠ b)
    (ab : AxisPair) :
    singleton p ab v =
      if ab.val.1 ≠ a ∧ ab.val.1 ≠ b ∧ ab.val.2 ≠ a ∧ ab.val.2 ≠ b ∧
        ¬ InPath p (flip ab.val.2 (flip ab.val.1 v)) then 1 else 0 := by
  classical
  unfold SquareIncidence.singleton
  congr 1
  apply propext
  constructor
  · rintro ⟨_,h1,h2,h3⟩
    exact ⟨(fun h => h1 (h ▸ ha)), (fun h => h1 (h ▸ hb)),
      (fun h => h2 (h ▸ ha)), (fun h => h2 (h ▸ hb)), h3⟩
  · rintro ⟨h1a,h1b,h2a,h2b,h3⟩
    exact ⟨hv,other_coordinate_absent p v a b _ hv ha hb hab h1a h1b,
      other_coordinate_absent p v a b _ hv ha hb hab h2a h2b,h3⟩

/-- This is the abstract alpha/counter identity; the instance's ordered list
of 21 corners still needs a finite bijection to these eligible axis pairs. -/
theorem localAlpha_eligible {m : Nat} (p : Snake m) (i : Fin (m+1))
    (a b : Coord) (ha : InPath p (flip a (p.vertex i)))
    (hb : InPath p (flip b (p.vertex i))) (hab : a ≠ b) :
    localAlpha p i = ∑ ab : AxisPair,
      if ab.val.1 ≠ a ∧ ab.val.1 ≠ b ∧ ab.val.2 ≠ a ∧ ab.val.2 ≠ b ∧
        ¬ InPath p (flip ab.val.2 (flip ab.val.1 (p.vertex i))) then 1 else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro ab _
  exact singleton_eligible p _ a b ⟨i,rfl⟩ ha hb hab ab

/-- Any duplicate-free ordered enumeration of eligible pairs gives exactly
the missing-corner list used by the counter, independent of its ordering. -/
theorem localAlpha_corner_list {m : Nat} (p : Snake m) (i : Fin (m+1))
    (a b : Coord) (ha : InPath p (flip a (p.vertex i)))
    (hb : InPath p (flip b (p.vertex i))) (hab : a ≠ b)
    (pairs : List AxisPair) (hn : pairs.Nodup)
    (hmem : ∀ ab : AxisPair, ab ∈ pairs ↔
      ab.val.1 ≠ a ∧ ab.val.1 ≠ b ∧ ab.val.2 ≠ a ∧ ab.val.2 ≠ b) :
    localAlpha p i = ((pairs.map (fun ab =>
      flip ab.val.2 (flip ab.val.1 (p.vertex i)))).filter
      (fun v => decide (¬ InPath p v))).length := by
  classical
  rw [localAlpha_eligible p i a b ha hb hab, Finset.sum_boole]
  rw [List.filter_map, List.length_map]
  rw [← List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist))]
  simp only [Nat.cast_id]
  apply congrArg Finset.card
  ext ab
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.comp_apply, decide_eq_true_eq, hmem]
  tauto

#print axioms localAlpha_corner_list
#print axioms other_coordinate_absent
#print axioms singleton_eligible
#print axioms localAlpha_eligible
end
end Snake9.Window244
