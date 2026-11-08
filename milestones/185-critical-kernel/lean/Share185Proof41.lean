import Share185Proof40
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem old_clause {cl : List Nat} (ho : oldLits M cl = true)
    (h : clauseTrue (tau S E M cs) (cl.map decodeLit) = true) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  unfold clauseTrue at h ⊢
  rw [List.any_map, List.any_eq_true] at h ⊢
  obtain ⟨a, ha, hv⟩ := h
  refine ⟨a, ha, ?_⟩
  simp only [oldLits, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ho
  obtain ⟨h2, hv2⟩ := ho a ha
  simp only [Function.comp] at hv ⊢
  rw [decode_eq _ h2] at hv ⊢
  rwa [lv_congr (τ₂ := tau S E M cs) (tauS_old hv2)]


/-! ### Clause families -/





end Snake9.LocalWindow.Tags185
