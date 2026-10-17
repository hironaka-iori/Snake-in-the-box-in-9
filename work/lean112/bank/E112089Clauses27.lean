import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 228 = true ∨ valuation q 97 = true ∨ valuation q 106 = true := by
  rw [value97, value104, value106, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(396 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (413 : Vertex) [(396 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 228 = true ∨ valuation q 97 = true ∨ valuation q 105 = true := by
  rw [value97, value104, value105, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(396 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (414 : Vertex) [(396 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 98 = false ∨ valuation q 104 = false ∨ valuation q 123 = false := by
  rw [value98, value104, value105, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (397 : Vertex) (412 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 229 = true ∨ valuation q 104 = true ∨ valuation q 123 = true := by
  rw [value104, value105, value123, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(412 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (397 : Vertex) [(412 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 230 = true ∨ valuation q 104 = true := by
  rw [value104, value106, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(412 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (406 : Vertex) [(412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 230 = true ∨ valuation q 103 = true := by
  rw [value103, value106, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(406 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (412 : Vertex) [(406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 90 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value90, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (384 : Vertex) (449 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 90 = false ∨ valuation q 108 = false ∨ valuation q 110 = false := by
  rw [value90, value107, value108, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (384 : Vertex) (449 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 90 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value90, value107, value109, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (384 : Vertex) (450 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 90 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value90, value107, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (384 : Vertex) (452 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value107, value108, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (449 : Vertex) (452 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 231 = true ∨ valuation q 90 = true ∨ valuation q 109 = true ∨ valuation q 110 = true ∨ valuation q 112 = true := by
  rw [value90, value107, value109, value110, value112, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(384 : Vertex), (450 : Vertex), (452 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (449 : Vertex) [(384 : Vertex), (450 : Vertex), (452 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 56 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value56, value107, value108, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (448 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 232 = true ∨ valuation q 56 = true ∨ valuation q 107 = true := by
  rw [value56, value107, value108, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(193 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (457 : Vertex) [(193 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 57 = false ∨ valuation q 91 = false ∨ valuation q 107 = false := by
  rw [value57, value91, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (386 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 57 = false ∨ valuation q 91 = false ∨ valuation q 111 = false := by
  rw [value57, value91, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (386 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 57 = false ∨ valuation q 107 = false ∨ valuation q 111 = false := by
  rw [value57, value107, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (448 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 91 = false ∨ valuation q 107 = false ∨ valuation q 111 = false := by
  rw [value91, value107, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (448 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 233 = true ∨ valuation q 57 = true ∨ valuation q 91 = true ∨ valuation q 107 = true := by
  rw [value57, value91, value107, value109, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (454 : Vertex) → w ∈ [(194 : Vertex), (386 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (454 : Vertex) [(194 : Vertex), (386 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 107 = false ∨ valuation q 111 = false ∨ valuation q 117 = false := by
  rw [value107, value110, value111, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (448 : Vertex) (454 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 234 = true ∨ valuation q 107 = true ∨ valuation q 117 = true := by
  rw [value107, value110, value117, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (452 : Vertex) w → w ∈ region → w ≠ (454 : Vertex) → w ∈ [(448 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (452 : Vertex) (454 : Vertex) [(448 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 234 = true ∨ valuation q 107 = true ∨ valuation q 111 = true := by
  rw [value107, value110, value111, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (452 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(448 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (452 : Vertex) (468 : Vertex) [(448 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 60 = true ∨ valuation q 109 = true ∨ valuation q 110 = true ∨ valuation q 114 = true := by
  rw [value60, value109, value110, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ∈ [(198 : Vertex), (450 : Vertex), (452 : Vertex), (462 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (454 : Vertex) [(198 : Vertex), (450 : Vertex), (452 : Vertex), (462 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 60 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value60, value110, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (198 : Vertex) (452 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value109, value110, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (450 : Vertex) (452 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 109 = true ∨ valuation q 110 = true ∨ valuation q 114 = true := by
  rw [value109, value110, value111, value114, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(450 : Vertex), (452 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (198 : Vertex) [(450 : Vertex), (452 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 60 = true ∨ valuation q 110 = true ∨ valuation q 114 = true := by
  rw [value60, value110, value111, value114, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(198 : Vertex), (452 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (450 : Vertex) [(198 : Vertex), (452 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 60 = true ∨ valuation q 109 = true ∨ valuation q 114 = true := by
  rw [value60, value109, value111, value114, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(198 : Vertex), (450 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (452 : Vertex) [(198 : Vertex), (450 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 60 = true ∨ valuation q 109 = true ∨ valuation q 110 = true := by
  rw [value60, value109, value110, value111, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(198 : Vertex), (450 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (462 : Vertex) [(198 : Vertex), (450 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 62 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value62, value107, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (448 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 62 = false ∨ valuation q 107 = false ∨ valuation q 120 = false := by
  rw [value62, value107, value112, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (448 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 62 = false ∨ valuation q 113 = false ∨ valuation q 120 = false := by
  rw [value62, value112, value113, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (457 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E089.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112089
