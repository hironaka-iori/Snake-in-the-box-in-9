import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 49 = false ∨ valuation q 62 = false ∨ valuation q 101 = false := by
  rw [value49, value50, value62, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (192 : Vertex) (209 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 52 = true ∨ valuation q 56 = true := by
  rw [value51, value52, value56, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(195 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (192 : Vertex) [(195 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 49 = true ∨ valuation q 56 = true := by
  rw [value49, value51, value56, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(192 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (195 : Vertex) [(192 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 49 = true ∨ valuation q 52 = true := by
  rw [value49, value51, value52, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(192 : Vertex), (195 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (202 : Vertex) [(192 : Vertex), (195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 30 = false ∨ valuation q 50 = false := by
  rw [value13, value30, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (131 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 30 = false ∨ valuation q 51 = false := by
  rw [value13, value30, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (131 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 30 = false ∨ valuation q 54 = false := by
  rw [value13, value30, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (131 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 30 = false ∨ valuation q 63 = false := by
  rw [value13, value30, value52, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (131 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 30 = false ∨ valuation q 102 = false := by
  rw [value13, value30, value52, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (131 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value13, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (193 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 50 = false ∨ valuation q 54 = false := by
  rw [value13, value50, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (193 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 50 = false ∨ valuation q 63 = false := by
  rw [value13, value50, value52, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (193 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 50 = false ∨ valuation q 102 = false := by
  rw [value13, value50, value52, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (193 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value13, value51, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (194 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 51 = false ∨ valuation q 63 = false := by
  rw [value13, value51, value52, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (194 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 51 = false ∨ valuation q 102 = false := by
  rw [value13, value51, value52, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (194 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 54 = false ∨ valuation q 63 = false := by
  rw [value13, value52, value54, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (199 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 54 = false ∨ valuation q 102 = false := by
  rw [value13, value52, value54, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (199 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 63 = false ∨ valuation q 102 = false := by
  rw [value13, value52, value63, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (211 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 30 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value30, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (193 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 30 = false ∨ valuation q 50 = false ∨ valuation q 54 = false := by
  rw [value30, value50, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (193 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 30 = false ∨ valuation q 50 = false ∨ valuation q 63 = false := by
  rw [value30, value50, value52, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (193 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 30 = false ∨ valuation q 50 = false ∨ valuation q 102 = false := by
  rw [value30, value50, value52, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (193 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 30 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value30, value51, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (194 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 30 = false ∨ valuation q 51 = false ∨ valuation q 63 = false := by
  rw [value30, value51, value52, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (194 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 30 = false ∨ valuation q 51 = false ∨ valuation q 102 = false := by
  rw [value30, value51, value52, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (194 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 30 = false ∨ valuation q 54 = false ∨ valuation q 63 = false := by
  rw [value30, value52, value54, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (199 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 30 = false ∨ valuation q 54 = false ∨ valuation q 102 = false := by
  rw [value30, value52, value54, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (199 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 30 = false ∨ valuation q 63 = false ∨ valuation q 102 = false := by
  rw [value30, value52, value63, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (211 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value50, value51, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (194 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 63 = false := by
  rw [value50, value51, value52, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (194 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 102 = false := by
  rw [value50, value51, value52, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (194 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E158.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112158
