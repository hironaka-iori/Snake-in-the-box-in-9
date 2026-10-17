import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 37 = false ∨ valuation q 81 = false ∨ valuation q 96 = false := by
  rw [value37, value81, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (417 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 39 = false ∨ valuation q 56 = false ∨ valuation q 93 = false := by
  rw [value39, value56, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 39 = false ∨ valuation q 56 = false ∨ valuation q 97 = false := by
  rw [value39, value56, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 39 = false ∨ valuation q 56 = false ∨ valuation q 101 = false := by
  rw [value39, value56, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 39 = false ∨ valuation q 56 = false ∨ valuation q 114 = false := by
  rw [value39, value56, value94, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 39 = false ∨ valuation q 93 = false ∨ valuation q 97 = false := by
  rw [value39, value93, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 39 = false ∨ valuation q 93 = false ∨ valuation q 101 = false := by
  rw [value39, value93, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 39 = false ∨ valuation q 93 = false ∨ valuation q 114 = false := by
  rw [value39, value93, value94, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 39 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value39, value94, value97, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 39 = false ∨ valuation q 101 = false ∨ valuation q 114 = false := by
  rw [value39, value94, value101, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 56 = false ∨ valuation q 93 = false ∨ valuation q 97 = false := by
  rw [value56, value93, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 56 = false ∨ valuation q 93 = false ∨ valuation q 101 = false := by
  rw [value56, value93, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 56 = false ∨ valuation q 93 = false ∨ valuation q 114 = false := by
  rw [value56, value93, value94, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 56 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value56, value94, value97, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 56 = false ∨ valuation q 97 = false ∨ valuation q 114 = false := by
  rw [value56, value94, value97, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 56 = false ∨ valuation q 101 = false ∨ valuation q 114 = false := by
  rw [value56, value94, value101, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 93 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value93, value94, value97, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 93 = false ∨ valuation q 97 = false ∨ valuation q 114 = false := by
  rw [value93, value94, value97, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 93 = false ∨ valuation q 101 = false ∨ valuation q 114 = false := by
  rw [value93, value94, value101, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 114 = false := by
  rw [value94, value97, value101, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (439 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 213 = true ∨ valuation q 39 = true ∨ valuation q 93 = true ∨ valuation q 97 = true ∨ valuation q 101 = true ∨ valuation q 114 = true := by
  rw [value39, value93, value94, value97, value101, value114, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(179 : Vertex), (433 : Vertex), (439 : Vertex), (443 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (307 : Vertex) [(179 : Vertex), (433 : Vertex), (439 : Vertex), (443 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 95 = true := by
  rw [value95, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (436 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 57 = true ∨ valuation q 83 = true ∨ valuation q 96 = true := by
  rw [value57, value83, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ∈ [(308 : Vertex), (420 : Vertex), (437 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (436 : Vertex) [(308 : Vertex), (420 : Vertex), (437 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 214 = true ∨ valuation q 83 = true ∨ valuation q 96 = true := by
  rw [value83, value95, value96, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(420 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (308 : Vertex) [(420 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 214 = true ∨ valuation q 57 = true ∨ valuation q 96 = true := by
  rw [value57, value95, value96, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(308 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (420 : Vertex) [(308 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 214 = true ∨ valuation q 57 = true ∨ valuation q 83 = true := by
  rw [value57, value83, value95, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(308 : Vertex), (420 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (437 : Vertex) [(308 : Vertex), (420 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 84 = false ∨ valuation q 93 = false ∨ valuation q 95 = false := by
  rw [value84, value93, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (433 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 84 = false ∨ valuation q 93 = false ∨ valuation q 97 = false := by
  rw [value84, value93, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 84 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value84, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (436 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 93 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value93, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (433 : Vertex) (436 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 97 = true := by
  rw [value97, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (439 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 86 = true ∨ valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 102 = true := by
  rw [value86, value94, value96, value97, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ∈ [(423 : Vertex), (435 : Vertex), (437 : Vertex), (447 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (439 : Vertex) [(423 : Vertex), (435 : Vertex), (437 : Vertex), (447 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block9 (q : Snake 81) (h : Conditions q) : B112E187.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112187
