import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 102 = false := by
  rw [value47, value48, value52, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (194 : Vertex) (200 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 102 = false := by
  rw [value47, value49, value52, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (196 : Vertex) (200 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 171 = true ∨ valuation q 49 = true ∨ valuation q 52 = true ∨ valuation q 102 = true := by
  rw [value47, value49, value52, value102, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(196 : Vertex), (200 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (194 : Vertex) [(196 : Vertex), (200 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 171 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 102 = true := by
  rw [value47, value48, value52, value102, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (196 : Vertex) → w ∈ [(194 : Vertex), (200 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (196 : Vertex) [(194 : Vertex), (200 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 171 = true ∨ valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 102 = true := by
  rw [value47, value48, value49, value102, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(194 : Vertex), (196 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (200 : Vertex) [(194 : Vertex), (196 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 48 = true := by
  rw [value48, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (194 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 47 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 104 = true := by
  rw [value47, value48, value51, value53, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ∈ [(192 : Vertex), (198 : Vertex), (202 : Vertex), (450 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (194 : Vertex) [(192 : Vertex), (198 : Vertex), (202 : Vertex), (450 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 104 = false := by
  rw [value47, value48, value51, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (192 : Vertex) (198 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 104 = false := by
  rw [value48, value51, value53, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (198 : Vertex) (202 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 47 = false ∨ valuation q 51 = false := by
  rw [value47, value51, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (194 : Vertex) (192 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 53 = false ∨ valuation q 104 = false := by
  rw [value53, value104, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (194 : Vertex) (202 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 172 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 104 = true := by
  rw [value48, value51, value53, value104, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(198 : Vertex), (202 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (192 : Vertex) [(198 : Vertex), (202 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 172 = true ∨ valuation q 47 = true ∨ valuation q 53 = true ∨ valuation q 104 = true := by
  rw [value47, value48, value53, value104, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(192 : Vertex), (202 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (198 : Vertex) [(192 : Vertex), (202 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 172 = true ∨ valuation q 47 = true ∨ valuation q 51 = true ∨ valuation q 104 = true := by
  rw [value47, value48, value51, value104, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(192 : Vertex), (198 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (202 : Vertex) [(192 : Vertex), (198 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 172 = true ∨ valuation q 47 = true ∨ valuation q 51 = true ∨ valuation q 53 = true := by
  rw [value47, value48, value51, value53, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(192 : Vertex), (198 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (450 : Vertex) [(192 : Vertex), (198 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 32 = false ∨ valuation q 47 = false := by
  rw [value14, value32, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (68 : Vertex) (132 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 32 = false ∨ valuation q 50 = false := by
  rw [value14, value32, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (68 : Vertex) (132 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 32 = false ∨ valuation q 55 = false := by
  rw [value14, value32, value49, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (68 : Vertex) (132 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value14, value47, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (68 : Vertex) (192 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 47 = false ∨ valuation q 51 = false := by
  rw [value14, value47, value49, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (68 : Vertex) (192 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 47 = false ∨ valuation q 55 = false := by
  rw [value14, value47, value49, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (68 : Vertex) (192 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value14, value49, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (68 : Vertex) (197 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value14, value49, value50, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (68 : Vertex) (197 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 14 = false ∨ valuation q 51 = false ∨ valuation q 55 = false := by
  rw [value14, value49, value51, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (68 : Vertex) (198 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 32 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value32, value47, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (132 : Vertex) (192 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 32 = false ∨ valuation q 47 = false ∨ valuation q 51 = false := by
  rw [value32, value47, value49, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (132 : Vertex) (192 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 32 = false ∨ valuation q 47 = false ∨ valuation q 55 = false := by
  rw [value32, value47, value49, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (132 : Vertex) (192 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 32 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value32, value49, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (132 : Vertex) (197 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 32 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value32, value49, value50, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (132 : Vertex) (197 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 32 = false ∨ valuation q 51 = false ∨ valuation q 55 = false := by
  rw [value32, value49, value51, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (132 : Vertex) (198 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value47, value49, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (192 : Vertex) (197 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value47, value49, value50, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (192 : Vertex) (197 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E105.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112105
