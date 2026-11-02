import LocalWindowTags

/-!
The sequential-counter proof from LocalWindowTags, with the counter's
base-literal and numerical bounds supplied explicitly. The assignment,
clause checker, geometry and counter semantics are unchanged.
-/
namespace Snake9.CounterSound111
open Snake9.LocalWindow Snake9.LocalWindow.Tags

set_option maxHeartbeats 2000000

section Families
variable {S E : Nat → Bool} {M : MT} {cs : List Ctr}
variable {w : List Nat} {cens : List Centre}

theorem sound_first {cl : List Nat} {c i : Nat}
    (h : ckFirst M cs c i cl = true)
    (hbase : ∀ c i, i < (cs.getD c dfltCtr).lits.length →
      baseOK M ((cs.getD c dfltCtr).lits.getD i 0) = true) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a, b], h =>
    simp only [ckFirst, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, ha⟩, hb⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp)
    rw [lit_negOf ha (hbase c i hi), Bool.not_eq_false'] at fa
    rw [lit_posR hb, decide_eq_false_iff_not] at fb
    apply fb
    unfold pc; rw [take_succ_countP hi, if_pos fa]; omega

theorem sound_step {cl : List Nat} {c i j : Nat}
    (h : ckStep M cs c i j cl = true)
    (hbase : ∀ c i, i < (cs.getD c dfltCtr).lits.length →
      baseOK M ((cs.getD c dfltCtr).lits.getD i 0) = true) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a, b, d], h =>
    simp only [ckStep, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, ha⟩, hb⟩, hd⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp); have fd := hf d (by simp)
    rw [lit_negOf ha (hbase c (i+1) hi), Bool.not_eq_false'] at fa
    rw [lit_negR hb, Bool.not_eq_false', decide_eq_true_eq] at fb
    rw [lit_posR hd, decide_eq_false_iff_not] at fd
    rw [pc_succ hi, if_pos fa] at fd
    omega

theorem sound_over {cl : List Nat} {c i : Nat}
    (h : ckOver M cs c i cl = true)
    (hbase : ∀ c i, i < (cs.getD c dfltCtr).lits.length →
      baseOK M ((cs.getD c dfltCtr).lits.getD i 0) = true)
    (hb : ∀ c, (cs.getD c dfltCtr).lits.countP (lv (base S E M)) ≤
      (cs.getD c dfltCtr).k) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a, b], h =>
    simp only [ckOver, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, ha⟩, hk⟩, hreg⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp)
    rw [lit_negOf ha (hbase c (i+1) hi), Bool.not_eq_false'] at fa
    rw [lit_negR hreg, Bool.not_eq_false', decide_eq_true_eq] at fb
    have h1 := pc_succ (S := S) (E := E) (M := M) hi
    rw [if_pos fa] at h1
    have h2 := pc_le_total (S := S) (E := E) (M := M)
      (cs.getD c dfltCtr).lits (i+1)
    have h3 := hb c
    omega

theorem sound_clause {t : Tag} {cl : List Nat}
    (h : ckClause M cs w t cl = true)
    (hbase : ∀ c i, i < (cs.getD c dfltCtr).lits.length →
      baseOK M ((cs.getD c dfltCtr).lits.getD i 0) = true)
    (hb : ∀ c, (cs.getD c dfltCtr).lits.countP (lv (base S E M)) ≤
      (cs.getD c dfltCtr).k)
    (ax : Axioms S E w cens) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  cases t with
  | window => exact Tags.sound_window h ax
  | deg2 => exact Tags.sound_deg2 h ax
  | degPos => exact Tags.sound_degPos h ax
  | endSel => exact Tags.sound_endSel h ax
  | lowEnd t => exact Tags.sound_lowEnd h ax
  | endLow => exact Tags.sound_endLow h ax
  | cut => exact Tags.sound_cut h ax
  | first c i => exact CounterSound111.sound_first h hbase
  | zero c j => exact Tags.sound_zero h
  | mono c i j => exact Tags.sound_mono h
  | step c i j => exact CounterSound111.sound_step h hbase
  | over c i => exact CounterSound111.sound_over h hbase hb

theorem sound_all : ∀ {tags : List Tag} {raw : List (List Nat)},
    ckAll M cs w tags raw = true →
    (∀ c i, i < (cs.getD c dfltCtr).lits.length →
      baseOK M ((cs.getD c dfltCtr).lits.getD i 0) = true) →
    (∀ c, (cs.getD c dfltCtr).lits.countP (lv (base S E M)) ≤
      (cs.getD c dfltCtr).k) →
    Axioms S E w cens →
    ∀ cl ∈ raw, clauseTrue (tau S E M cs) (cl.map decodeLit) = true
  | [], [], _, _, _, _ => by simp
  | t :: ts, cl :: cls, h, hbase, hb, ax => by
    simp only [ckAll, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact CounterSound111.sound_clause h.1 hbase hb ax
    · exact CounterSound111.sound_all h.2 hbase hb ax x hx
  | [], _ :: _, h, _, _, _ => by simp [ckAll] at h
  | _ :: _, [], h, _, _, _ => by simp [ckAll] at h

end Families

theorem sound (M : MT) (cs : List Ctr) (w : List Nat)
    (b : List (Nat × Nat)) (tags : List Tag) (raw : List (List Nat))
    (h : ckAll M cs w tags raw = true) (S E : Nat → Bool)
    (hbase : ∀ c i, i < (cs.getD c dfltCtr).lits.length →
      baseOK M ((cs.getD c dfltCtr).lits.getD i 0) = true)
    (hb : ∀ c, (cs.getD c dfltCtr).lits.countP (lv (base S E M)) ≤
      (cs.getD c dfltCtr).k)
    (ax : Axioms S E w (centresOf w b)) :
    cnfTrue (tau S E M cs) (raw.map (·.map decodeLit)) = true := by
  unfold cnfTrue
  rw [List.all_map, List.all_eq_true]
  intro cl hcl
  exact CounterSound111.sound_all h hbase hb ax cl hcl

#print axioms sound_first
#print axioms sound_step
#print axioms sound_over
#print axioms sound_clause
#print axioms sound_all
#print axioms sound
end Snake9.CounterSound111
