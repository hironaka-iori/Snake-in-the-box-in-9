import Share185Proof31
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem nb_pos {w : List Nat} {cens : List Centre} {t : Tot} {q : Nat}
    (h : totOK M X w cens t = true) (hk : t.kind = .nb q) (hw : ∀ v ∈ w, S v = true) :
    1 ≤ cnt S (nbrs q) := by
  unfold totOK at h
  rw [hk] at h
  simp only [Bool.and_eq_true, List.any_eq_true, List.contains_iff_mem, and_assoc] at h
  obtain ⟨_, _, _, v, hv, hvw⟩ := h
  unfold cnt
  rw [← List.countP_eq_length_filter]
  exact List.countP_pos_iff.2 ⟨v, hv, hw v hvw⟩


end Snake9.LocalWindow.Tags185
