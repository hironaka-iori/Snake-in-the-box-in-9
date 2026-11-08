import Share185Proof51
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sound_allS {cap : Nat} : ∀ {tags : List TagS} {raw : List (List Nat)},
    ckAllS M X Mr cs tots w cap tags raw = true →
    cs.all (ctrOK M cens) = true → tots.all (totOK M X w cens) = true →
    AxiomsS S E w cens Mr cap →
    ∀ cl ∈ raw, clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true
  | [], [], _, _, _, _ => by simp
  | t :: ts, cl :: cls, h, hcs, ht, ax => by
    simp only [ckAllS, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact sound_clauseS h.1 hcs ht ax
    · exact sound_allS h.2 hcs ht ax x hx
  | [], _ :: _, h, _, _, _ => by simp [ckAllS] at h
  | _ :: _, [], h, _, _, _ => by simp [ckAllS] at h




end Snake9.LocalWindow.Tags185
