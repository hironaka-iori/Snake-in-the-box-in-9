import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 1 = true ∨ valuation q 70 = true ∨ valuation q 75 = true := by
  rw [value1, value70, value71, value75, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(33 : Vertex), (288 : Vertex), (297 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (417 : Vertex) [(33 : Vertex), (288 : Vertex), (297 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 73 = false ∨ valuation q 77 = false := by
  rw [value73, value77, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (294 : Vertex) (295 : Vertex) (302 : Vertex) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 196 = true ∨ valuation q 73 = true := by
  rw [value72, value73, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (294 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(295 : Vertex)] := by decide
  have hg := other_cover q (294 : Vertex) (302 : Vertex) [(295 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 4 = false ∨ valuation q 72 = false ∨ valuation q 81 = false := by
  rw [value4, value72, value73, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (39 : Vertex) (294 : Vertex) (311 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 72 = false ∨ valuation q 81 = false ∨ valuation q 91 = false := by
  rw [value72, value73, value81, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (294 : Vertex) (311 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 197 = true ∨ valuation q 4 = true ∨ valuation q 81 = true ∨ valuation q 91 = true := by
  rw [value4, value73, value81, value91, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(39 : Vertex), (311 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (294 : Vertex) [(39 : Vertex), (311 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 70 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value70, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (297 : Vertex) (300 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 70 = false ∨ valuation q 76 = false ∨ valuation q 92 = false := by
  rw [value70, value74, value76, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (300 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 92 = false := by
  rw [value74, value75, value76, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (297 : Vertex) (300 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 75 = true ∨ valuation q 76 = true ∨ valuation q 92 = true := by
  rw [value74, value75, value76, value92, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(297 : Vertex), (300 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (288 : Vertex) [(297 : Vertex), (300 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 70 = true ∨ valuation q 76 = true ∨ valuation q 92 = true := by
  rw [value70, value74, value76, value92, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(288 : Vertex), (300 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (297 : Vertex) [(288 : Vertex), (300 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 70 = true ∨ valuation q 75 = true ∨ valuation q 92 = true := by
  rw [value70, value74, value75, value92, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (300 : Vertex) → w ∈ [(288 : Vertex), (297 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (300 : Vertex) [(288 : Vertex), (297 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 5 = false ∨ valuation q 71 = false ∨ valuation q 74 = false := by
  rw [value5, value71, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (41 : Vertex) (289 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 5 = false ∨ valuation q 71 = false ∨ valuation q 82 = false := by
  rw [value5, value71, value75, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (41 : Vertex) (289 : Vertex) (313 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 5 = false ∨ valuation q 74 = false ∨ valuation q 82 = false := by
  rw [value5, value74, value75, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (41 : Vertex) (296 : Vertex) (313 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 71 = false ∨ valuation q 74 = false ∨ valuation q 82 = false := by
  rw [value71, value74, value75, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (289 : Vertex) (296 : Vertex) (313 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 94 = false := by
  rw [value74, value76, value77, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (300 : Vertex) (296 : Vertex) (302 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 74 = false ∨ valuation q 77 = false := by
  rw [value74, value77, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (300 : Vertex) (296 : Vertex) (302 : Vertex) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 77 = true ∨ valuation q 94 = true := by
  rw [value76, value77, value94, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (300 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(302 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (300 : Vertex) (296 : Vertex) [(302 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 74 = true ∨ valuation q 94 = true := by
  rw [value74, value76, value94, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (300 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(296 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (300 : Vertex) (302 : Vertex) [(296 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 201 = true ∨ valuation q 76 = true ∨ valuation q 96 = true := by
  rw [value76, value77, value96, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(300 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (294 : Vertex) [(300 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 201 = true ∨ valuation q 72 = true ∨ valuation q 96 = true := by
  rw [value72, value77, value96, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (300 : Vertex) → w ∈ [(294 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (300 : Vertex) [(294 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 83 = false ∨ valuation q 100 = false := by
  rw [value83, value100, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (306 : Vertex) (314 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 100 = true := by
  rw [value78, value100, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (306 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(434 : Vertex)] := by decide
  have hg := other_cover q (306 : Vertex) (314 : Vertex) [(434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 12 = false ∨ valuation q 80 = false ∨ valuation q 102 = false := by
  rw [value12, value79, value80, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (52 : Vertex) (309 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 85 = false := by
  rw [value79, value80, value81, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (309 : Vertex) (308 : Vertex) (311 : Vertex) (317 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 204 = true ∨ valuation q 81 = true ∨ valuation q 85 = true := by
  rw [value80, value81, value85, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (309 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(311 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (309 : Vertex) (308 : Vertex) [(311 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 204 = true ∨ valuation q 79 = true ∨ valuation q 85 = true := by
  rw [value79, value80, value85, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (309 : Vertex) w → w ∈ region → w ≠ (311 : Vertex) → w ∈ [(308 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (309 : Vertex) (311 : Vertex) [(308 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 204 = true ∨ valuation q 79 = true ∨ valuation q 81 = true := by
  rw [value79, value80, value81, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (309 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(308 : Vertex), (311 : Vertex)] := by decide
  have hg := other_cover q (309 : Vertex) (317 : Vertex) [(308 : Vertex), (311 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 13 = false ∨ valuation q 73 = false ∨ valuation q 80 = false := by
  rw [value13, value73, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (311 : Vertex) (55 : Vertex) (295 : Vertex) (309 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 205 = true ∨ valuation q 13 = true ∨ valuation q 73 = true := by
  rw [value13, value73, value81, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (311 : Vertex) w → w ∈ region → w ≠ (309 : Vertex) → w ∈ [(55 : Vertex), (295 : Vertex)] := by decide
  have hg := other_cover q (311 : Vertex) (309 : Vertex) [(55 : Vertex), (295 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 75 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value75, value82, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (313 : Vertex) (297 : Vertex) (315 : Vertex) (317 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E008.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112008
