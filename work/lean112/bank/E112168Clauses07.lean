import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 162 = true ∨ valuation q 10 = true ∨ valuation q 29 = true ∨ valuation q 43 = true ∨ valuation q 51 = true ∨ valuation q 101 = true := by
  rw [value10, value29, value43, value48, value51, value101, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(73 : Vertex), (137 : Vertex), (193 : Vertex), (205 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (217 : Vertex) [(73 : Vertex), (137 : Vertex), (193 : Vertex), (205 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 11 = false ∨ valuation q 30 = false ∨ valuation q 44 = false := by
  rw [value11, value30, value44, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (138 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 11 = false ∨ valuation q 30 = false ∨ valuation q 52 = false := by
  rw [value11, value30, value49, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (138 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 11 = false ∨ valuation q 30 = false ∨ valuation q 61 = false := by
  rw [value11, value30, value49, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (138 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 11 = false ∨ valuation q 30 = false ∨ valuation q 102 = false := by
  rw [value11, value30, value49, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (138 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 11 = false ∨ valuation q 44 = false ∨ valuation q 61 = false := by
  rw [value11, value44, value49, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (194 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 11 = false ∨ valuation q 44 = false ∨ valuation q 102 = false := by
  rw [value11, value44, value49, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (194 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 11 = false ∨ valuation q 52 = false ∨ valuation q 61 = false := by
  rw [value11, value49, value52, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (206 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 11 = false ∨ valuation q 52 = false ∨ valuation q 102 = false := by
  rw [value11, value49, value52, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (206 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 11 = false ∨ valuation q 61 = false ∨ valuation q 102 = false := by
  rw [value11, value49, value61, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (218 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 30 = false ∨ valuation q 44 = false ∨ valuation q 61 = false := by
  rw [value30, value44, value49, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (138 : Vertex) (194 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 30 = false ∨ valuation q 44 = false ∨ valuation q 102 = false := by
  rw [value30, value44, value49, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (138 : Vertex) (194 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 30 = false ∨ valuation q 52 = false ∨ valuation q 61 = false := by
  rw [value30, value49, value52, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (138 : Vertex) (206 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 61 = false ∨ valuation q 102 = false := by
  rw [value49, value52, value61, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (206 : Vertex) (218 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 12 = false ∨ valuation q 31 = false ∨ valuation q 51 = false := by
  rw [value12, value31, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 12 = false ∨ valuation q 31 = false ∨ valuation q 52 = false := by
  rw [value12, value31, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 12 = false ∨ valuation q 31 = false ∨ valuation q 62 = false := by
  rw [value12, value31, value50, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 12 = false ∨ valuation q 31 = false ∨ valuation q 104 = false := by
  rw [value12, value31, value50, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 12 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value12, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 12 = false ∨ valuation q 51 = false ∨ valuation q 62 = false := by
  rw [value12, value50, value51, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (205 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 12 = false ∨ valuation q 51 = false ∨ valuation q 104 = false := by
  rw [value12, value50, value51, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (205 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 12 = false ∨ valuation q 52 = false ∨ valuation q 62 = false := by
  rw [value12, value50, value52, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (206 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 12 = false ∨ valuation q 52 = false ∨ valuation q 104 = false := by
  rw [value12, value50, value52, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (206 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 12 = false ∨ valuation q 62 = false ∨ valuation q 104 = false := by
  rw [value12, value50, value62, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (220 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 31 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value31, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 31 = false ∨ valuation q 51 = false ∨ valuation q 62 = false := by
  rw [value31, value50, value51, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (205 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 31 = false ∨ valuation q 51 = false ∨ valuation q 104 = false := by
  rw [value31, value50, value51, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (205 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 31 = false ∨ valuation q 52 = false ∨ valuation q 62 = false := by
  rw [value31, value50, value52, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (206 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 31 = false ∨ valuation q 62 = false ∨ valuation q 104 = false := by
  rw [value31, value50, value62, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (220 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 62 = false := by
  rw [value50, value51, value52, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (205 : Vertex) (206 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 104 = false := by
  rw [value50, value51, value52, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (205 : Vertex) (206 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 104 = false := by
  rw [value50, value51, value62, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (205 : Vertex) (220 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E168.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112168
