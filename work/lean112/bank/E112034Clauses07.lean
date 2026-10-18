import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 72 = false := by
  rw [value51, value53, value54, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (289 : Vertex) (292 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 51 = false ∨ valuation q 61 = false ∨ valuation q 72 = false := by
  rw [value51, value54, value61, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (289 : Vertex) (309 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = false ∨ valuation q 61 = false ∨ valuation q 72 = false := by
  rw [value53, value54, value61, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (292 : Vertex) (309 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 60 = false := by
  rw [value52, value53, value55, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (290 : Vertex) (292 : Vertex) (302 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 62 = false := by
  rw [value52, value53, value55, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (290 : Vertex) (292 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value52, value55, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (290 : Vertex) (302 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 53 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value53, value55, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (292 : Vertex) (302 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 183 = true ∨ valuation q 53 = true ∨ valuation q 60 = true ∨ valuation q 62 = true := by
  rw [value53, value55, value60, value62, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (294 : Vertex) w → w ∈ region → w ≠ (290 : Vertex) → w ∈ [(292 : Vertex), (302 : Vertex), (310 : Vertex)] := by decide
  have hg := other_cover q (294 : Vertex) (290 : Vertex) [(292 : Vertex), (302 : Vertex), (310 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 183 = true ∨ valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 60 = true := by
  rw [value52, value53, value55, value60, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (294 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(290 : Vertex), (292 : Vertex), (302 : Vertex)] := by decide
  have hg := other_cover q (294 : Vertex) (310 : Vertex) [(290 : Vertex), (292 : Vertex), (302 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 184 = true ∨ valuation q 50 = true ∨ valuation q 57 = true ∨ valuation q 64 = true := by
  rw [value50, value56, value57, value64, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (300 : Vertex) → w ∈ [(288 : Vertex), (298 : Vertex), (312 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (300 : Vertex) [(288 : Vertex), (298 : Vertex), (312 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 184 = true ∨ valuation q 50 = true ∨ valuation q 57 = true ∨ valuation q 59 = true := by
  rw [value50, value56, value57, value59, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (312 : Vertex) → w ∈ [(288 : Vertex), (298 : Vertex), (300 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (312 : Vertex) [(288 : Vertex), (298 : Vertex), (300 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 52 = false ∨ valuation q 56 = false ∨ valuation q 58 = false := by
  rw [value52, value56, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (290 : Vertex) (296 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 52 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value52, value56, value57, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (290 : Vertex) (296 : Vertex) (302 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 52 = false ∨ valuation q 56 = false ∨ valuation q 74 = false := by
  rw [value52, value56, value57, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (290 : Vertex) (296 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 52 = false ∨ valuation q 56 = false ∨ valuation q 93 = false := by
  rw [value52, value56, value57, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (290 : Vertex) (296 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 52 = false ∨ valuation q 58 = false ∨ valuation q 60 = false := by
  rw [value52, value57, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (290 : Vertex) (299 : Vertex) (302 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 52 = false ∨ valuation q 58 = false ∨ valuation q 74 = false := by
  rw [value52, value57, value58, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (290 : Vertex) (299 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 52 = false ∨ valuation q 58 = false ∨ valuation q 93 = false := by
  rw [value52, value57, value58, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (290 : Vertex) (299 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 52 = false ∨ valuation q 60 = false ∨ valuation q 74 = false := by
  rw [value52, value57, value60, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (290 : Vertex) (302 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 52 = false ∨ valuation q 60 = false ∨ valuation q 93 = false := by
  rw [value52, value57, value60, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (290 : Vertex) (302 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 52 = false ∨ valuation q 74 = false ∨ valuation q 93 = false := by
  rw [value52, value57, value74, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (290 : Vertex) (362 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 60 = false := by
  rw [value56, value57, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (296 : Vertex) (299 : Vertex) (302 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 74 = false := by
  rw [value56, value57, value58, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (296 : Vertex) (299 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 93 = false := by
  rw [value56, value57, value58, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (296 : Vertex) (299 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 56 = false ∨ valuation q 60 = false ∨ valuation q 74 = false := by
  rw [value56, value57, value60, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (296 : Vertex) (302 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 56 = false ∨ valuation q 60 = false ∨ valuation q 93 = false := by
  rw [value56, value57, value60, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (296 : Vertex) (302 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 56 = false ∨ valuation q 74 = false ∨ valuation q 93 = false := by
  rw [value56, value57, value74, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (296 : Vertex) (362 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 74 = false := by
  rw [value57, value58, value60, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (299 : Vertex) (302 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 93 = false := by
  rw [value57, value58, value60, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (299 : Vertex) (302 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 74 = false ∨ valuation q 93 = false := by
  rw [value57, value58, value74, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (299 : Vertex) (362 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 60 = false ∨ valuation q 74 = false ∨ valuation q 93 = false := by
  rw [value57, value60, value74, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (298 : Vertex) (302 : Vertex) (362 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 186 = true ∨ valuation q 57 = true ∨ valuation q 66 = true ∨ valuation q 75 = true := by
  rw [value57, value58, value66, value75, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (43 : Vertex) → w ∈ [(298 : Vertex), (315 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (43 : Vertex) [(298 : Vertex), (315 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E034.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112034
