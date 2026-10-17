import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 20 = false ∨ valuation q 79 = false ∨ valuation q 88 = false := by
  rw [value20, value79, value80, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (388 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 20 = false ∨ valuation q 79 = false ∨ valuation q 100 = false := by
  rw [value20, value79, value80, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (388 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 20 = false ∨ valuation q 88 = false ∨ valuation q 100 = false := by
  rw [value20, value80, value88, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (405 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 77 = false ∨ valuation q 79 = false ∨ valuation q 88 = false := by
  rw [value77, value79, value80, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (388 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 77 = false ∨ valuation q 79 = false ∨ valuation q 100 = false := by
  rw [value77, value79, value80, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (388 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 77 = false ∨ valuation q 88 = false ∨ valuation q 100 = false := by
  rw [value77, value80, value88, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (405 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 79 = false ∨ valuation q 88 = false ∨ valuation q 100 = false := by
  rw [value79, value80, value88, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (388 : Vertex) (405 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 86 = false := by
  rw [value78, value79, value81, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 89 = false := by
  rw [value78, value79, value81, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 78 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value78, value81, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (398 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 79 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value79, value81, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (388 : Vertex) (398 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 199 = true ∨ valuation q 78 = true ∨ valuation q 79 = true ∨ valuation q 86 = true := by
  rw [value78, value79, value81, value86, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(386 : Vertex), (388 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (406 : Vertex) [(386 : Vertex), (388 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 200 = true ∨ valuation q 76 = true ∨ valuation q 83 = true ∨ valuation q 91 = true ∨ valuation q 102 = true := by
  rw [value76, value82, value83, value91, value102, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(384 : Vertex), (394 : Vertex), (408 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (396 : Vertex) [(384 : Vertex), (394 : Vertex), (408 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 200 = true ∨ valuation q 76 = true ∨ valuation q 83 = true ∨ valuation q 85 = true ∨ valuation q 102 = true := by
  rw [value76, value82, value83, value85, value102, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(384 : Vertex), (394 : Vertex), (396 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (408 : Vertex) [(384 : Vertex), (394 : Vertex), (396 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 200 = true ∨ valuation q 76 = true ∨ valuation q 83 = true ∨ valuation q 85 = true ∨ valuation q 91 = true := by
  rw [value76, value82, value83, value85, value91, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(384 : Vertex), (394 : Vertex), (396 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (456 : Vertex) [(384 : Vertex), (394 : Vertex), (396 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 22 = false ∨ valuation q 52 = false ∨ valuation q 78 = false := by
  rw [value22, value52, value78, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (266 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 22 = false ∨ valuation q 52 = false ∨ valuation q 82 = false := by
  rw [value22, value52, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (266 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 22 = false ∨ valuation q 52 = false ∨ valuation q 84 = false := by
  rw [value22, value52, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (266 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 22 = false ∨ valuation q 52 = false ∨ valuation q 86 = false := by
  rw [value22, value52, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (266 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 22 = false ∨ valuation q 78 = false ∨ valuation q 82 = false := by
  rw [value22, value78, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (386 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 22 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value22, value78, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (386 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 22 = false ∨ valuation q 78 = false ∨ valuation q 86 = false := by
  rw [value22, value78, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (386 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 22 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value22, value82, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (392 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 22 = false ∨ valuation q 82 = false ∨ valuation q 86 = false := by
  rw [value22, value82, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 22 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value22, value83, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (395 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value52, value78, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (386 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 78 = false ∨ valuation q 86 = false := by
  rw [value52, value78, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (386 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value52, value82, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (392 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value52, value83, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (395 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 78 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value78, value82, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (392 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 78 = false ∨ valuation q 82 = false ∨ valuation q 86 = false := by
  rw [value78, value82, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 78 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value78, value83, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (395 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E110.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112110
