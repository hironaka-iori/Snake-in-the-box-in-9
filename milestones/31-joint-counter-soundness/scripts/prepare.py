"""Generalize three existing counter-clause proofs to explicit count premises."""
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
for d in ['lean','logs','data']:(HERE/d).mkdir(exist_ok=True)
s=(ROOT/'milestones/28-direct-share-certificates/upstream/LocalWindowTags.lean').read_text(encoding='utf-8')
pieces=[]
for start,end in [('theorem sound_first','theorem sound_zero'),('theorem sound_step','theorem sound_over'),('theorem sound_over','theorem sound_clause'),('theorem sound_clause','end Families')]:
    pieces.append(s[s.index(start):s.index(end,s.index(start))])
families='\n'.join(pieces)
families=families.replace('cs.all (ctrOK M cens) = true','Valid S E M cs')
families=families.replace('ctr_lit_ok (ctrOK_getD hcs c) hi','valid_lit hcs c hi')
families=families.replace('ctr_bound (ctrOK_getD hcs c) ax','(hcs c).2')
prefix='''import LocalWindowTags
import Mathlib.Tactic

namespace Snake9.LocalWindow.JointTags
open Tags

/-- Semantic counter conditions: primitive inputs and a bound on their true
occurrences. Repeated literals count repeatedly. -/
def Good (S E : Nat → Bool) (M : MT) (ct : Ctr) : Prop :=
  ct.lits.all (baseOK M) = true ∧ ct.lits.countP (lv (base S E M)) ≤ ct.k

def Valid (S E : Nat → Bool) (M : MT) (cs : List Ctr) : Prop :=
  ∀ c, Good S E M (cs.getD c dfltCtr)

variable {S E : Nat → Bool} {M : MT} {cs : List Ctr} {w : List Nat} {cens : List Centre}

theorem valid_lit (hcs : Valid S E M cs) (c : Nat) {i : Nat}
    (hi : i < (cs.getD c dfltCtr).lits.length) :
    baseOK M ((cs.getD c dfltCtr).lits.getD i 0) = true :=
  List.all_eq_true.1 (hcs c).1 _ (getD_mem hi)

theorem valid_of_all (h : ∀ ct ∈ cs, Good S E M ct) : Valid S E M cs := by
  intro c
  rw [List.getD_eq_getElem?_getD]
  cases hc : cs[c]? with
  | none => simp [Good, dfltCtr]
  | some ct => exact h ct (List.mem_of_getElem? hc)

theorem valid_append {old extra : List Ctr}
    (ho : old.all (ctrOK M cens) = true)
    (he : ∀ ct ∈ extra, Good S E M ct) (ax : Axioms S E w cens) :
    Valid S E M (old ++ extra) := by
  apply valid_of_all
  intro ct hc
  rcases List.mem_append.mp hc with hc | hc
  · have hct := List.all_eq_true.1 ho ct hc
    have hb := ctr_bound hct ax
    unfold ctrOK at hct
    rw [Bool.and_eq_true] at hct
    exact ⟨hct.1, hb⟩
  · exact he ct hc

'''
suffix='''
/-- Clause soundness with arbitrary additional counters whose actual input
counts are bounded. This theorem does not assert any new geometric bound. -/
theorem sound (M : MT) (cs : List Ctr) (w : List Nat) (cens : List Centre)
    (tags : List Tag) (raw : List (List Nat))
    (h : ckAll M cs w tags raw = true) (S E : Nat → Bool)
    (hcs : Valid S E M cs) (ax : Axioms S E w cens) :
    cnfTrue (tau S E M cs) (raw.map (·.map decodeLit)) = true := by
  unfold cnfTrue
  rw [List.all_map, List.all_eq_true]
  intro cl hcl
  exact sound_all h hcs ax cl hcl

/-- Concatenating opposite-corner lists adds singleton counts, including
the multiplicities of corner vertices shared between centres. -/
theorem three_centre_count (lits : List Nat) (a b c : Centre)
    (hn : lits.all (negP M) = true)
    (hm : lits.map (vl M) = corners a ++ corners b ++ corners c) :
    lits.countP (lv (base S E M)) =
      absentCorners S a.v a.d₁ a.d₂ + absentCorners S b.v b.d₁ b.d₂ +
        absentCorners S c.v c.d₁ c.d₂ := by
  have h : lits.countP (lv (base S E M)) = (lits.map (vl M)).countP (fun v => !S v) := by
    rw [List.countP_map]
    apply List.countP_congr
    intro x hx
    simp [base_negP (List.all_eq_true.1 hn x hx)]
  rw [h, hm]
  simp only [List.countP_append, countP_corners_abs]

#print axioms valid_lit
#print axioms valid_of_all
#print axioms valid_append
#print axioms sound_first
#print axioms sound_step
#print axioms sound_over
#print axioms sound_clause
#print axioms sound_all
#print axioms sound
#print axioms three_centre_count
end Snake9.LocalWindow.JointTags
'''
(HERE/'lean/JointCountTags.lean').write_text(prefix+families+suffix,encoding='utf-8')
print('Prepared generalized counter soundness source.')
