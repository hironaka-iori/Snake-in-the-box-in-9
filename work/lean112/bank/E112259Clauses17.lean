import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 210 = true ∨ valuation q 72 = true ∨ valuation q 90 = true := by
  rw [value72, value90, value94, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(157 : Vertex), (181 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (185 : Vertex) [(157 : Vertex), (181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 35 = false ∨ valuation q 73 = false ∨ valuation q 93 = false := by
  rw [value35, value73, value93, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (158 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 211 = true ∨ valuation q 73 = true ∨ valuation q 93 = true := by
  rw [value73, value93, value95, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (62 : Vertex) → w ∈ [(158 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (62 : Vertex) [(158 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 211 = true ∨ valuation q 35 = true ∨ valuation q 93 = true := by
  rw [value35, value93, value95, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(62 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (158 : Vertex) [(62 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 211 = true ∨ valuation q 35 = true ∨ valuation q 73 = true := by
  rw [value35, value73, value95, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(62 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (186 : Vertex) [(62 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value97, value101, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (199 : Vertex) (207 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 212 = true ∨ valuation q 101 = true := by
  rw [value96, value101, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(215 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (207 : Vertex) [(215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 212 = true ∨ valuation q 97 = true := by
  rw [value96, value97, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (215 : Vertex) [(207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 213 = true ∨ valuation q 96 = true := by
  rw [value96, value97, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(199 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (79 : Vertex) [(199 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 213 = true ∨ valuation q 37 = true := by
  rw [value37, value97, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(79 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (199 : Vertex) [(79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 214 = true ∨ valuation q 99 = true := by
  rw [value98, value99, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(209 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (80 : Vertex) [(209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 214 = true ∨ valuation q 38 = true := by
  rw [value38, value98, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(80 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (209 : Vertex) [(80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 215 = true ∨ valuation q 102 = true := by
  rw [value99, value102, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(217 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (208 : Vertex) [(217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 215 = true ∨ valuation q 98 = true := by
  rw [value98, value99, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(208 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (217 : Vertex) [(208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 69 = false ∨ valuation q 101 = false ∨ valuation q 114 = false := by
  rw [value69, value100, value101, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (214 : Vertex) (150 : Vertex) (215 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 217 = true ∨ valuation q 96 = true ∨ valuation q 100 = true := by
  rw [value96, value100, value101, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(199 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (87 : Vertex) [(199 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 217 = true ∨ valuation q 41 = true ∨ valuation q 100 = true := by
  rw [value41, value100, value101, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(87 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (199 : Vertex) [(87 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 218 = true ∨ valuation q 99 = true := by
  rw [value99, value102, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(209 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (89 : Vertex) [(209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 218 = true ∨ valuation q 42 = true := by
  rw [value42, value102, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(89 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (209 : Vertex) [(89 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 219 = true ∨ valuation q 104 = true := by
  rw [value103, value104, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(225 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (160 : Vertex) [(225 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 219 = true ∨ valuation q 75 = true := by
  rw [value75, value103, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (225 : Vertex) → w ∈ [(160 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (225 : Vertex) [(160 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value103, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (224 : Vertex) (227 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 220 = true ∨ valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 107 = true := by
  rw [value103, value104, value105, value107, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(224 : Vertex), (227 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (161 : Vertex) [(224 : Vertex), (227 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 220 = true ∨ valuation q 76 = true ∨ valuation q 105 = true ∨ valuation q 107 = true := by
  rw [value76, value104, value105, value107, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (224 : Vertex) → w ∈ [(161 : Vertex), (227 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (224 : Vertex) [(161 : Vertex), (227 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 220 = true ∨ valuation q 76 = true ∨ valuation q 103 = true ∨ valuation q 107 = true := by
  rw [value76, value103, value104, value107, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(161 : Vertex), (224 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (227 : Vertex) [(161 : Vertex), (224 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 220 = true ∨ valuation q 76 = true ∨ valuation q 103 = true ∨ valuation q 105 = true := by
  rw [value76, value103, value104, value105, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(161 : Vertex), (224 : Vertex), (227 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (233 : Vertex) [(161 : Vertex), (224 : Vertex), (227 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 78 = false ∨ valuation q 104 = false ∨ valuation q 112 = false := by
  rw [value78, value104, value105, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (163 : Vertex) (225 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 222 = true ∨ valuation q 114 = true := by
  rw [value106, value114, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(246 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (238 : Vertex) [(246 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 44 = false ∨ valuation q 104 = false := by
  rw [value44, value104, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (233 : Vertex) (105 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 223 = true ∨ valuation q 104 = true ∨ valuation q 108 = true ∨ valuation q 109 = true := by
  rw [value104, value107, value108, value109, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(225 : Vertex), (235 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (105 : Vertex) [(225 : Vertex), (235 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 223 = true ∨ valuation q 44 = true ∨ valuation q 108 = true ∨ valuation q 109 = true := by
  rw [value44, value107, value108, value109, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (225 : Vertex) → w ∈ [(105 : Vertex), (235 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (225 : Vertex) [(105 : Vertex), (235 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 45 = false ∨ valuation q 105 = false ∨ valuation q 115 = false := by
  rw [value45, value105, value108, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (227 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E259.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112259
