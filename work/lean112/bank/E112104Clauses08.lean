import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 91 = true ∨ valuation q 95 = true := by
  rw [value91, value94, value95, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(438 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (442 : Vertex) [(438 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 118 = false := by
  rw [value93, value94, value95, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (445 : Vertex) (446 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 213 = true ∨ valuation q 94 = true ∨ valuation q 118 = true := by
  rw [value94, value95, value118, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (445 : Vertex) → w ∈ [(446 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (445 : Vertex) [(446 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 213 = true ∨ valuation q 93 = true ∨ valuation q 118 = true := by
  rw [value93, value95, value118, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(445 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (446 : Vertex) [(445 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value96, value97, value99, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (482 : Vertex) (484 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 214 = true ∨ valuation q 99 = true ∨ valuation q 102 = true := by
  rw [value96, value99, value102, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [(484 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (482 : Vertex) [(484 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 98 = true ∨ valuation q 100 = true ∨ valuation q 104 = true := by
  rw [value97, value98, value100, value104, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(483 : Vertex), (486 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (480 : Vertex) [(483 : Vertex), (486 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 96 = true ∨ valuation q 100 = true ∨ valuation q 104 = true := by
  rw [value96, value97, value100, value104, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(480 : Vertex), (486 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (483 : Vertex) [(480 : Vertex), (486 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 96 = true ∨ valuation q 98 = true ∨ valuation q 104 = true := by
  rw [value96, value97, value98, value104, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(480 : Vertex), (483 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (486 : Vertex) [(480 : Vertex), (483 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 96 = true ∨ valuation q 98 = true ∨ valuation q 100 = true := by
  rw [value96, value97, value98, value100, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(480 : Vertex), (483 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (490 : Vertex) [(480 : Vertex), (483 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 31 = false ∨ valuation q 63 = false ∨ valuation q 80 = false := by
  rw [value31, value63, value80, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 31 = false ∨ valuation q 63 = false ∨ valuation q 97 = false := by
  rw [value31, value63, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 31 = false ∨ valuation q 63 = false ∨ valuation q 101 = false := by
  rw [value31, value63, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 31 = false ∨ valuation q 63 = false ∨ valuation q 105 = false := by
  rw [value31, value63, value98, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 31 = false ∨ valuation q 63 = false ∨ valuation q 109 = false := by
  rw [value31, value63, value98, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 31 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value31, value97, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (482 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 31 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value31, value97, value98, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (482 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 31 = false ∨ valuation q 97 = false ∨ valuation q 109 = false := by
  rw [value31, value97, value98, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 31 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value31, value98, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (487 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 31 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value31, value98, value101, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (487 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 31 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value31, value98, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 63 = false ∨ valuation q 80 = false ∨ valuation q 97 = false := by
  rw [value63, value80, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (419 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 63 = false ∨ valuation q 80 = false ∨ valuation q 101 = false := by
  rw [value63, value80, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (419 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 63 = false ∨ valuation q 80 = false ∨ valuation q 105 = false := by
  rw [value63, value80, value98, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (419 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 63 = false ∨ valuation q 80 = false ∨ valuation q 109 = false := by
  rw [value63, value80, value98, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (419 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 63 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value63, value97, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (482 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 63 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value63, value97, value98, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (482 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 63 = false ∨ valuation q 97 = false ∨ valuation q 109 = false := by
  rw [value63, value97, value98, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 63 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value63, value98, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (487 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 63 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value63, value98, value101, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (487 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 63 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value63, value98, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 80 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value80, value97, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (419 : Vertex) (482 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E104.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112104
