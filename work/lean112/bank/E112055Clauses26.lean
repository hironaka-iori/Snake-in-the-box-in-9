import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 118 = false := by
  rw [value109, value110, value111, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (386 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 237 = true ∨ valuation q 111 = true ∨ valuation q 118 = true := by
  rw [value109, value111, value118, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(386 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (385 : Vertex) [(386 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 237 = true ∨ valuation q 110 = true ∨ valuation q 118 = true := by
  rw [value109, value110, value118, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(385 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (386 : Vertex) [(385 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 237 = true ∨ valuation q 110 = true ∨ valuation q 111 = true := by
  rw [value109, value110, value111, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(385 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (400 : Vertex) [(385 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 109 = false ∨ valuation q 112 = false ∨ valuation q 119 = false := by
  rw [value109, value110, value112, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (384 : Vertex) (389 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 238 = true ∨ valuation q 112 = true ∨ valuation q 119 = true := by
  rw [value110, value112, value119, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(389 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (384 : Vertex) [(389 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 238 = true ∨ valuation q 109 = true ∨ valuation q 119 = true := by
  rw [value109, value110, value119, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(384 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (389 : Vertex) [(384 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 238 = true ∨ valuation q 109 = true ∨ valuation q 112 = true := by
  rw [value109, value110, value112, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(384 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (401 : Vertex) [(384 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 239 = true ∨ valuation q 113 = true := by
  rw [value111, value113, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (384 : Vertex) [(394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 239 = true ∨ valuation q 109 = true := by
  rw [value109, value111, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(384 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (394 : Vertex) [(384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 40 = false ∨ valuation q 71 = false ∨ valuation q 110 = false := by
  rw [value40, value71, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 40 = false ∨ valuation q 71 = false ∨ valuation q 115 = false := by
  rw [value40, value71, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 40 = false ∨ valuation q 110 = false ∨ valuation q 115 = false := by
  rw [value40, value110, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (385 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 71 = false ∨ valuation q 110 = false ∨ valuation q 115 = false := by
  rw [value71, value110, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (385 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 240 = true ∨ valuation q 40 = true ∨ valuation q 71 = true ∨ valuation q 115 = true := by
  rw [value40, value71, value112, value115, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(133 : Vertex), (261 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (385 : Vertex) [(133 : Vertex), (261 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 240 = true ∨ valuation q 40 = true ∨ valuation q 71 = true ∨ valuation q 110 = true := by
  rw [value40, value71, value110, value112, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(133 : Vertex), (261 : Vertex), (385 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (397 : Vertex) [(133 : Vertex), (261 : Vertex), (385 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 45 = false ∨ valuation q 111 = false ∨ valuation q 116 = false := by
  rw [value45, value111, value113, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (386 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 241 = true ∨ valuation q 45 = true ∨ valuation q 116 = true := by
  rw [value45, value113, value116, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(138 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (386 : Vertex) [(138 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 241 = true ∨ valuation q 45 = true ∨ valuation q 111 = true := by
  rw [value45, value111, value113, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(138 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (398 : Vertex) [(138 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 77 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value77, value114, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (397 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 77 = false ∨ valuation q 115 = false ∨ valuation q 125 = false := by
  rw [value77, value114, value115, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 77 = false ∨ valuation q 116 = false ∨ valuation q 125 = false := by
  rw [value77, value114, value116, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (398 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 115 = false ∨ valuation q 116 = false ∨ valuation q 125 = false := by
  rw [value114, value115, value116, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (397 : Vertex) (398 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 242 = true ∨ valuation q 77 = true ∨ valuation q 116 = true ∨ valuation q 125 = true := by
  rw [value77, value114, value116, value125, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(268 : Vertex), (398 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (397 : Vertex) [(268 : Vertex), (398 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 242 = true ∨ valuation q 77 = true ∨ valuation q 115 = true ∨ valuation q 125 = true := by
  rw [value77, value114, value115, value125, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(268 : Vertex), (397 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (398 : Vertex) [(268 : Vertex), (397 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 242 = true ∨ valuation q 77 = true ∨ valuation q 115 = true ∨ valuation q 116 = true := by
  rw [value77, value114, value115, value116, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(268 : Vertex), (397 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (412 : Vertex) [(268 : Vertex), (397 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 47 = false ∨ valuation q 78 = false ∨ valuation q 112 = false := by
  rw [value47, value78, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (269 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 47 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value47, value112, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (389 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 47 = false ∨ valuation q 112 = false ∨ valuation q 117 = false := by
  rw [value47, value112, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (389 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 78 = false ∨ valuation q 112 = false ∨ valuation q 117 = false := by
  rw [value78, value112, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (389 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 78 = true ∨ valuation q 112 = true ∨ valuation q 114 = true ∨ valuation q 117 = true := by
  rw [value78, value112, value114, value115, value117, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(269 : Vertex), (389 : Vertex), (396 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (141 : Vertex) [(269 : Vertex), (389 : Vertex), (396 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 47 = true ∨ valuation q 112 = true ∨ valuation q 114 = true ∨ valuation q 117 = true := by
  rw [value47, value112, value114, value115, value117, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(141 : Vertex), (389 : Vertex), (396 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (269 : Vertex) [(141 : Vertex), (389 : Vertex), (396 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block26 (q : Snake 81) (h : Conditions q) : B112E055.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112055
