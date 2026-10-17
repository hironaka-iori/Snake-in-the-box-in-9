import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 63 = false ∨ valuation q 79 = false ∨ valuation q 80 = false := by
  rw [value63, value79, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (287 : Vertex) (349 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 72 = false ∨ valuation q 80 = false ∨ valuation q 124 = false := by
  rw [value72, value80, value81, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (335 : Vertex) (350 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 94 = false := by
  rw [value82, value83, value84, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (386 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 105 = false := by
  rw [value82, value83, value84, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (386 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 94 = false ∨ valuation q 105 = false := by
  rw [value82, value83, value94, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (400 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 88 = false := by
  rw [value83, value85, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (387 : Vertex) (389 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 95 = false := by
  rw [value83, value86, value88, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (389 : Vertex) (393 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 85 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 95 = true := by
  rw [value83, value85, value86, value88, value95, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(387 : Vertex), (389 : Vertex), (393 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (384 : Vertex) [(387 : Vertex), (389 : Vertex), (393 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 82 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 95 = true := by
  rw [value82, value83, value86, value88, value95, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(384 : Vertex), (389 : Vertex), (393 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (387 : Vertex) [(384 : Vertex), (389 : Vertex), (393 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 88 = true ∨ valuation q 95 = true := by
  rw [value82, value83, value85, value88, value95, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(384 : Vertex), (387 : Vertex), (393 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (389 : Vertex) [(384 : Vertex), (387 : Vertex), (393 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 86 = true ∨ valuation q 95 = true := by
  rw [value82, value83, value85, value86, value95, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(384 : Vertex), (387 : Vertex), (389 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (393 : Vertex) [(384 : Vertex), (387 : Vertex), (389 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 86 = true ∨ valuation q 88 = true := by
  rw [value82, value83, value85, value86, value88, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(384 : Vertex), (387 : Vertex), (389 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (401 : Vertex) [(384 : Vertex), (387 : Vertex), (389 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 12 = false ∨ valuation q 47 = false ∨ valuation q 82 = false := by
  rw [value12, value47, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (258 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 12 = false ∨ valuation q 47 = false ∨ valuation q 85 = false := by
  rw [value12, value47, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (258 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 12 = false ∨ valuation q 47 = false ∨ valuation q 89 = false := by
  rw [value12, value47, value84, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (258 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 12 = false ∨ valuation q 47 = false ∨ valuation q 96 = false := by
  rw [value12, value47, value84, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (258 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 12 = false ∨ valuation q 47 = false ∨ valuation q 106 = false := by
  rw [value12, value47, value84, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (258 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 12 = false ∨ valuation q 82 = false ∨ valuation q 106 = false := by
  rw [value12, value82, value84, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (384 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 12 = false ∨ valuation q 89 = false ∨ valuation q 96 = false := by
  rw [value12, value84, value89, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (394 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 12 = false ∨ valuation q 89 = false ∨ valuation q 106 = false := by
  rw [value12, value84, value89, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (394 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 12 = false ∨ valuation q 96 = false ∨ valuation q 106 = false := by
  rw [value12, value84, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (402 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 47 = false ∨ valuation q 82 = false ∨ valuation q 96 = false := by
  rw [value47, value82, value84, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (384 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 47 = false ∨ valuation q 82 = false ∨ valuation q 106 = false := by
  rw [value47, value82, value84, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (384 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 47 = false ∨ valuation q 85 = false ∨ valuation q 96 = false := by
  rw [value47, value84, value85, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (387 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 47 = false ∨ valuation q 96 = false ∨ valuation q 106 = false := by
  rw [value47, value84, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (402 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 89 = false ∨ valuation q 106 = false := by
  rw [value84, value85, value89, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (387 : Vertex) (394 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 208 = true ∨ valuation q 47 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 89 = true ∨ valuation q 96 = true ∨ valuation q 106 = true := by
  rw [value47, value82, value84, value85, value89, value96, value106, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(258 : Vertex), (384 : Vertex), (387 : Vertex), (394 : Vertex), (402 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (130 : Vertex) [(258 : Vertex), (384 : Vertex), (387 : Vertex), (394 : Vertex), (402 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 13 = true ∨ valuation q 48 = true ∨ valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 87 = true ∨ valuation q 97 = true ∨ valuation q 107 = true := by
  rw [value13, value48, value83, value84, value85, value87, value97, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (387 : Vertex) w → w ∈ region → w ∈ [(131 : Vertex), (259 : Vertex), (385 : Vertex), (386 : Vertex), (391 : Vertex), (403 : Vertex), (451 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (387 : Vertex) [(131 : Vertex), (259 : Vertex), (385 : Vertex), (386 : Vertex), (391 : Vertex), (403 : Vertex), (451 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 13 = false ∨ valuation q 48 = false ∨ valuation q 83 = false := by
  rw [value13, value48, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 13 = false ∨ valuation q 48 = false ∨ valuation q 84 = false := by
  rw [value13, value48, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 13 = false ∨ valuation q 48 = false ∨ valuation q 87 = false := by
  rw [value13, value48, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 13 = false ∨ valuation q 48 = false ∨ valuation q 97 = false := by
  rw [value13, value48, value85, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E186.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112186
