import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 198 = true ∨ valuation q 14 = true ∨ valuation q 71 = true ∨ valuation q 93 = true := by
  rw [value14, value71, value72, value93, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(39 : Vertex), (294 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (303 : Vertex) [(39 : Vertex), (294 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 15 = false ∨ valuation q 69 = false ∨ valuation q 74 = false := by
  rw [value15, value69, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (288 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 69 = false ∨ valuation q 74 = false ∨ valuation q 94 = false := by
  rw [value69, value73, value74, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (297 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 199 = true ∨ valuation q 15 = true ∨ valuation q 74 = true ∨ valuation q 94 = true := by
  rw [value15, value73, value74, value94, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(40 : Vertex), (297 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (288 : Vertex) [(40 : Vertex), (297 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 16 = false ∨ valuation q 70 = false ∨ valuation q 76 = false := by
  rw [value16, value70, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (41 : Vertex) (289 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 16 = false ∨ valuation q 73 = false ∨ valuation q 76 = false := by
  rw [value16, value73, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (41 : Vertex) (296 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 200 = true ∨ valuation q 16 = true ∨ valuation q 70 = true ∨ valuation q 73 = true ∨ valuation q 76 = true := by
  rw [value16, value70, value73, value74, value76, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (297 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(41 : Vertex), (289 : Vertex), (296 : Vertex), (301 : Vertex)] := by decide
  have hg := other_cover q (297 : Vertex) (299 : Vertex) [(41 : Vertex), (289 : Vertex), (296 : Vertex), (301 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 200 = true ∨ valuation q 16 = true ∨ valuation q 70 = true ∨ valuation q 73 = true ∨ valuation q 75 = true := by
  rw [value16, value70, value73, value74, value75, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (297 : Vertex) w → w ∈ region → w ≠ (301 : Vertex) → w ∈ [(41 : Vertex), (289 : Vertex), (296 : Vertex), (299 : Vertex)] := by decide
  have hg := other_cover q (297 : Vertex) (301 : Vertex) [(41 : Vertex), (289 : Vertex), (296 : Vertex), (299 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 96 = false := by
  rw [value74, value75, value77, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (299 : Vertex) (297 : Vertex) (303 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 85 = false := by
  rw [value74, value76, value77, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (301 : Vertex) (297 : Vertex) (303 : Vertex) (317 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 74 = false ∨ valuation q 77 = false := by
  rw [value74, value77, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (301 : Vertex) (297 : Vertex) (303 : Vertex) (by decide) (by decide) (by decide)

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 202 = true ∨ valuation q 74 = true ∨ valuation q 85 = true := by
  rw [value74, value76, value85, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(297 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (303 : Vertex) [(297 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 203 = true ∨ valuation q 75 = true ∨ valuation q 76 = true ∨ valuation q 99 = true := by
  rw [value75, value76, value77, value99, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (303 : Vertex) w → w ∈ region → w ≠ (295 : Vertex) → w ∈ [(299 : Vertex), (301 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (303 : Vertex) (295 : Vertex) [(299 : Vertex), (301 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 203 = true ∨ valuation q 72 = true ∨ valuation q 76 = true ∨ valuation q 99 = true := by
  rw [value72, value76, value77, value99, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (303 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(295 : Vertex), (301 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (303 : Vertex) (299 : Vertex) [(295 : Vertex), (301 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 203 = true ∨ valuation q 72 = true ∨ valuation q 75 = true ∨ valuation q 99 = true := by
  rw [value72, value75, value77, value99, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (303 : Vertex) w → w ∈ region → w ≠ (301 : Vertex) → w ∈ [(295 : Vertex), (299 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (303 : Vertex) (301 : Vertex) [(295 : Vertex), (299 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 20 = false ∨ valuation q 70 = false ∨ valuation q 100 = false := by
  rw [value20, value70, value78, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (49 : Vertex) (289 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 20 = false ∨ valuation q 80 = false ∨ valuation q 100 = false := by
  rw [value20, value78, value80, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (49 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 204 = true ∨ valuation q 70 = true ∨ valuation q 80 = true ∨ valuation q 100 = true := by
  rw [value70, value78, value80, value100, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(289 : Vertex), (307 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (49 : Vertex) [(289 : Vertex), (307 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 204 = true ∨ valuation q 20 = true ∨ valuation q 80 = true ∨ valuation q 100 = true := by
  rw [value20, value78, value80, value100, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(49 : Vertex), (307 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (289 : Vertex) [(49 : Vertex), (307 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 204 = true ∨ valuation q 20 = true ∨ valuation q 70 = true ∨ valuation q 100 = true := by
  rw [value20, value70, value78, value100, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(49 : Vertex), (289 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (307 : Vertex) [(49 : Vertex), (289 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 204 = true ∨ valuation q 20 = true ∨ valuation q 70 = true ∨ valuation q 80 = true := by
  rw [value20, value70, value78, value80, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(49 : Vertex), (289 : Vertex), (307 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (433 : Vertex) [(49 : Vertex), (289 : Vertex), (307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 21 = false ∨ valuation q 80 = false ∨ valuation q 83 = false := by
  rw [value21, value79, value80, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (50 : Vertex) (307 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 205 = true ∨ valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 83 = true := by
  rw [value79, value80, value82, value83, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (306 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(307 : Vertex), (310 : Vertex), (314 : Vertex)] := by decide
  have hg := other_cover q (306 : Vertex) (50 : Vertex) [(307 : Vertex), (310 : Vertex), (314 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 205 = true ∨ valuation q 21 = true ∨ valuation q 82 = true ∨ valuation q 83 = true := by
  rw [value21, value79, value82, value83, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (306 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(50 : Vertex), (310 : Vertex), (314 : Vertex)] := by decide
  have hg := other_cover q (306 : Vertex) (307 : Vertex) [(50 : Vertex), (310 : Vertex), (314 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 205 = true ∨ valuation q 21 = true ∨ valuation q 80 = true ∨ valuation q 83 = true := by
  rw [value21, value79, value80, value83, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (306 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(50 : Vertex), (307 : Vertex), (314 : Vertex)] := by decide
  have hg := other_cover q (306 : Vertex) (310 : Vertex) [(50 : Vertex), (307 : Vertex), (314 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 205 = true ∨ valuation q 21 = true ∨ valuation q 80 = true ∨ valuation q 82 = true := by
  rw [value21, value79, value80, value82, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (306 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(50 : Vertex), (307 : Vertex), (310 : Vertex)] := by decide
  have hg := other_cover q (306 : Vertex) (314 : Vertex) [(50 : Vertex), (307 : Vertex), (310 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 22 = true ∨ valuation q 78 = true ∨ valuation q 79 = true ∨ valuation q 101 = true := by
  rw [value22, value78, value79, value80, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ∈ [(51 : Vertex), (305 : Vertex), (306 : Vertex), (435 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (307 : Vertex) [(51 : Vertex), (305 : Vertex), (306 : Vertex), (435 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 22 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value22, value78, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (51 : Vertex) (305 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 22 = false ∨ valuation q 78 = false ∨ valuation q 101 = false := by
  rw [value22, value78, value80, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (51 : Vertex) (305 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 22 = false ∨ valuation q 79 = false ∨ valuation q 101 = false := by
  rw [value22, value79, value80, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (51 : Vertex) (306 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 101 = false := by
  rw [value78, value79, value80, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (305 : Vertex) (306 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 206 = true ∨ valuation q 22 = true ∨ valuation q 79 = true ∨ valuation q 101 = true := by
  rw [value22, value79, value80, value101, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(51 : Vertex), (306 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(51 : Vertex), (306 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block17 (q : Snake 81) (h : Conditions q) : B112E121.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112121
