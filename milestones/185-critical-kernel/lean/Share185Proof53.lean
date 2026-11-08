import Share185Proof52
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem soundS (M : MT) (X : MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot) (w : List Nat)
    (b : List (Nat × Nat)) (cap : Nat) (tags : List TagS) (raw : List (List Nat))
    (h : checkAllS M X Mr cs tots w b cap tags raw = true) (S E : Nat → Bool)
    (ax : AxiomsS S E w (centresOf w b) Mr cap) :
    cnfTrue (tauS S E M X Mr cs tots) (raw.map (·.map decodeLit)) = true := by
  simp only [checkAllS, Bool.and_eq_true] at h
  rw [centresK_eq] at ax
  unfold cnfTrue
  rw [List.all_map, List.all_eq_true]
  intro cl hcl
  exact sound_allS h.2 h.1.1 h.1.2 ax cl hcl



end Snake9.LocalWindow.Tags185
