import JointCountTags
import LocalWindowTagsShare

namespace Snake9.LocalWindow.PairShare
open Tags
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
  {w : List Nat} {cens shares : List Centre}

theorem sound_clause {cap : Nat} {t : TagS} {cl : List Nat}
    (h : ckClauseS M X Mr cs tots w cap t cl = true)
    (hcs : JointTags.Valid S E M cs) (ht : tots.all (totOK M X w shares) = true)
    (ax : Axioms S E w cens) (hs : shareSum Mr S shares ≤ cap) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  cases t with
  | old t =>
    simp only [ckClauseS, Bool.and_eq_true] at h
    exact old_clause h.1 (JointTags.sound_clause h.2 hcs ax)
  | emptyE => exact sound_emptyE h
  | totUp i => exact sound_totUp h ht
  | totDown i => exact sound_totDown h ht
  | shareCl eT dT => exact sound_shareCl h ht ax.window_sel
  | shareCap i => exact sound_shareCap h ht hs

theorem sound_all {cap : Nat} : ∀ {tags : List TagS} {raw : List (List Nat)},
    ckAllS M X Mr cs tots w cap tags raw = true →
    JointTags.Valid S E M cs → tots.all (totOK M X w shares) = true →
    Axioms S E w cens → (shareSum Mr S shares ≤ cap) →
    ∀ cl ∈ raw, clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true
  | [], [], _, _, _, _, _ => by simp
  | t :: ts, cl :: cls, h, hcs, ht, ax, hs => by
    simp only [ckAllS, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact sound_clause h.1 hcs ht ax hs
    · exact sound_all h.2 hcs ht ax hs x hx
  | [], _ :: _, h, _, _, _, _ => by simp [ckAllS] at h
  | _ :: _, [], h, _, _, _, _ => by simp [ckAllS] at h


theorem sound (M : MT) (X : MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot)
    (w : List Nat) (cens shares : List Centre) (cap : Nat)
    (tags : List TagS) (raw : List (List Nat))
    (hc : ckAllS M X Mr cs tots w cap tags raw = true)
    (ht : tots.all (totOK M X w shares) = true)
    (S E : Nat → Bool) (hv : JointTags.Valid S E M cs)
    (ax : Axioms S E w cens) (hs : shareSum Mr S shares ≤ cap) :
    cnfTrue (tauS S E M X Mr cs tots) (raw.map (·.map decodeLit)) = true := by
  unfold cnfTrue
  rw [List.all_map, List.all_eq_true]
  intro cl hcl
  exact sound_all hc hv ht ax hs cl hcl

#print axioms sound_clause
#print axioms sound_all
#print axioms sound
end Snake9.LocalWindow.PairShare
