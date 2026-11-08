import Share185Proof50
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sound_clauseS {cap : Nat} {t : TagS} {cl : List Nat}
    (h : ckClauseS M X Mr cs tots w cap t cl = true)
    (hcs : cs.all (ctrOK M cens) = true) (ht : tots.all (totOK M X w cens) = true)
    (ax : AxiomsS S E w cens Mr cap) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  cases t with
  | old t =>
    simp only [ckClauseS, Bool.and_eq_true] at h
    exact old_clause h.1 (sound_clause h.2 hcs ax.toAxioms)
  | emptyE => exact sound_emptyE h
  | totUp i => exact sound_totUp h ht
  | totDown i => exact sound_totDown h ht
  | shareCl eT dT => exact sound_shareCl h ht ax.window_sel
  | shareCap i => exact sound_shareCap h ht ax.share_le


end Snake9.LocalWindow.Tags185
