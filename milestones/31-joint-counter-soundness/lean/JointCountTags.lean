import LocalWindowTags
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

theorem sound_first {cl : List Nat} {c i : Nat} (h : ckFirst M cs c i cl = true)
    (hcs : Valid S E M cs) : clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a, b], h =>
    simp only [ckFirst, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, ha⟩, hb⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp)
    rw [lit_negOf ha (valid_lit hcs c hi), Bool.not_eq_false'] at fa
    rw [lit_posR hb, decide_eq_false_iff_not] at fb
    apply fb
    unfold pc; rw [take_succ_countP hi, if_pos fa]; omega


theorem sound_step {cl : List Nat} {c i j : Nat} (h : ckStep M cs c i j cl = true)
    (hcs : Valid S E M cs) : clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a, b, d], h =>
    simp only [ckStep, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, ha⟩, hb⟩, hd⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp); have fd := hf d (by simp)
    rw [lit_negOf ha (valid_lit hcs c hi), Bool.not_eq_false'] at fa
    rw [lit_negR hb, Bool.not_eq_false', decide_eq_true_eq] at fb
    rw [lit_posR hd, decide_eq_false_iff_not] at fd
    rw [pc_succ hi, if_pos fa] at fd
    omega


theorem sound_over {cl : List Nat} {c i : Nat} (h : ckOver M cs c i cl = true)
    (hcs : Valid S E M cs) (ax : Axioms S E w cens) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a, b], h =>
    simp only [ckOver, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, ha⟩, hk⟩, hb⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp)
    rw [lit_negOf ha (valid_lit hcs c hi), Bool.not_eq_false'] at fa
    rw [lit_negR hb, Bool.not_eq_false', decide_eq_true_eq] at fb
    have h1 := pc_succ (S := S) (E := E) (M := M) hi
    rw [if_pos fa] at h1
    have h2 := pc_le_total (S := S) (E := E) (M := M) (cs.getD c dfltCtr).lits (i + 1)
    have h3 := (hcs c).2
    omega


theorem sound_clause {t : Tag} {cl : List Nat} (h : ckClause M cs w t cl = true)
    (hcs : Valid S E M cs) (ax : Axioms S E w cens) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  cases t with
  | window => exact sound_window h ax
  | deg2 => exact sound_deg2 h ax
  | degPos => exact sound_degPos h ax
  | endSel => exact sound_endSel h ax
  | lowEnd t => exact sound_lowEnd h ax
  | endLow => exact sound_endLow h ax
  | cut => exact sound_cut h ax
  | first c i => exact sound_first h hcs
  | zero c j => exact sound_zero h
  | mono c i j => exact sound_mono h
  | step c i j => exact sound_step h hcs
  | over c i => exact sound_over h hcs ax

theorem sound_all : ∀ {tags : List Tag} {raw : List (List Nat)}, ckAll M cs w tags raw = true →
    Valid S E M cs → Axioms S E w cens →
    ∀ cl ∈ raw, clauseTrue (tau S E M cs) (cl.map decodeLit) = true
  | [], [], _, _, _ => by simp
  | t :: ts, cl :: cls, h, hcs, ax => by
    simp only [ckAll, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact sound_clause h.1 hcs ax
    · exact sound_all h.2 hcs ax x hx
  | [], _ :: _, h, _, _ => by simp [ckAll] at h
  | _ :: _, [], h, _, _ => by simp [ckAll] at h


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
