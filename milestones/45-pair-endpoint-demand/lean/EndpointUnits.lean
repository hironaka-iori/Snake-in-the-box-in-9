import JointCountTags

namespace Snake9.LocalWindow.EndpointUnits
open Tags

theorem sound (S E : Nat → Bool) (M : MT) (cs : List Ctr) (lits : List Nat)
    (hneg : lits.all (negE M) = true)
    (habs : ∀ l ∈ lits, E (vl M l) = false) :
    cnfTrue (tau S E M cs) ((lits.map (fun l => [l])).map (·.map decodeLit)) = true := by
  unfold cnfTrue
  rw [List.all_map, List.all_map, List.all_eq_true]
  intro l hl
  simp only [Function.comp_apply, List.map_cons, List.map_nil, clauseTrue,
    List.any_cons, List.any_nil, Bool.or_false]
  rw [lit_negE (List.all_eq_true.mp hneg l hl), habs l hl]
  rfl

#print axioms sound
end Snake9.LocalWindow.EndpointUnits
