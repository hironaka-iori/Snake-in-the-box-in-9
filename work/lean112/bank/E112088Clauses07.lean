import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 16 = false ∨ valuation q 33 = false ∨ valuation q 103 = false := by
  rw [value16, value33, value37, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (167 : Vertex) (227 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 16 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value16, value35, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (167 : Vertex) (229 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 16 = false ∨ valuation q 35 = false ∨ valuation q 47 = false := by
  rw [value16, value35, value37, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (167 : Vertex) (229 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 16 = false ∨ valuation q 35 = false ∨ valuation q 103 = false := by
  rw [value16, value35, value37, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (167 : Vertex) (229 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 16 = false ∨ valuation q 36 = false ∨ valuation q 47 = false := by
  rw [value16, value36, value37, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (167 : Vertex) (230 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 16 = false ∨ valuation q 36 = false ∨ valuation q 103 = false := by
  rw [value16, value36, value37, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (167 : Vertex) (230 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 16 = false ∨ valuation q 47 = false ∨ valuation q 103 = false := by
  rw [value16, value37, value47, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (167 : Vertex) (247 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value33, value35, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (227 : Vertex) (229 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 47 = false := by
  rw [value33, value35, value37, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (227 : Vertex) (229 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 103 = false := by
  rw [value33, value35, value37, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (227 : Vertex) (229 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 47 = false := by
  rw [value33, value36, value37, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (227 : Vertex) (230 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 103 = false := by
  rw [value33, value36, value37, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (227 : Vertex) (230 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 47 = false ∨ valuation q 103 = false := by
  rw [value33, value37, value47, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (227 : Vertex) (247 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 47 = false := by
  rw [value35, value36, value37, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (229 : Vertex) (230 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 103 = false := by
  rw [value35, value36, value37, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (229 : Vertex) (230 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 36 = false ∨ valuation q 47 = false ∨ valuation q 103 = false := by
  rw [value36, value37, value47, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (230 : Vertex) (247 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value32, value38, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (233 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 42 = false := by
  rw [value32, value38, value39, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (233 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 48 = false := by
  rw [value32, value38, value39, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (233 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 40 = false ∨ valuation q 42 = false := by
  rw [value32, value38, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (234 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 40 = false ∨ valuation q 48 = false := by
  rw [value32, value38, value40, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (234 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 42 = false ∨ valuation q 48 = false := by
  rw [value32, value38, value42, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (236 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 42 = false := by
  rw [value38, value39, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (233 : Vertex) (234 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 48 = false := by
  rw [value38, value39, value40, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (233 : Vertex) (234 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 48 = false := by
  rw [value38, value39, value42, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (233 : Vertex) (236 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 48 = false := by
  rw [value38, value40, value42, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (234 : Vertex) (236 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 154 = true ∨ valuation q 32 = true ∨ valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 48 = true := by
  rw [value32, value38, value40, value42, value48, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(224 : Vertex), (234 : Vertex), (236 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (233 : Vertex) [(224 : Vertex), (234 : Vertex), (236 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 154 = true ∨ valuation q 32 = true ∨ valuation q 39 = true ∨ valuation q 40 = true ∨ valuation q 48 = true := by
  rw [value32, value38, value39, value40, value48, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(224 : Vertex), (233 : Vertex), (234 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (236 : Vertex) [(224 : Vertex), (233 : Vertex), (234 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 154 = true ∨ valuation q 32 = true ∨ valuation q 39 = true ∨ valuation q 40 = true ∨ valuation q 42 = true := by
  rw [value32, value38, value39, value40, value42, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(224 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (248 : Vertex) [(224 : Vertex), (233 : Vertex), (234 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 17 = false ∨ valuation q 38 = false ∨ valuation q 41 = false := by
  rw [value17, value38, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (169 : Vertex) (232 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 17 = false ∨ valuation q 38 = false ∨ valuation q 49 = false := by
  rw [value17, value38, value39, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (169 : Vertex) (232 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 17 = false ∨ valuation q 41 = false ∨ valuation q 49 = false := by
  rw [value17, value39, value41, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (169 : Vertex) (235 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E088.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112088
