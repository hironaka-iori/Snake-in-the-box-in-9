import Share185Proof41
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sound_emptyE {cl : List Nat} (h : ckEmptyE M X cl = true) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  match cl, h with
  | [a1, a2, a3, a4, e], h =>
    simp only [ckEmptyE, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, he⟩, v1⟩, v2⟩, v3⟩, v4⟩ := h
    apply clause_intro; intro hf
    have f1 := hf a1 (by simp); have f2 := hf a2 (by simp)
    have f3 := hf a3 (by simp); have f4 := hf a4 (by simp); have fe := hf e (by simp)
    rw [lit_posP_S h1, v1] at f1
    rw [lit_posP_S h2, v2] at f2
    rw [lit_posP_S h3, v3] at f3
    rw [lit_posP_S h4, v4] at f4
    rw [lit_posSq he] at fe
    unfold emptyPred at fe
    rw [f1, f2, f3, f4] at fe
    exact absurd fe (by decide)


end Snake9.LocalWindow.Tags185
