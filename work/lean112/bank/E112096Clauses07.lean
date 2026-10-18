import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 82 = false ∨ valuation q 84 = false ∨ valuation q 105 = false := by
  rw [value82, value84, value85, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (393 : Vertex) (396 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 203 = true ∨ valuation q 84 = true ∨ valuation q 105 = true := by
  rw [value84, value85, value105, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(396 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (393 : Vertex) [(396 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 203 = true ∨ valuation q 82 = true ∨ valuation q 105 = true := by
  rw [value82, value85, value105, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(393 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (396 : Vertex) [(393 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 203 = true ∨ valuation q 82 = true ∨ valuation q 84 = true := by
  rw [value82, value84, value85, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(393 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (461 : Vertex) [(393 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value87, value88, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (403 : Vertex) (405 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 205 = true ∨ valuation q 88 = true ∨ valuation q 92 = true := by
  rw [value87, value88, value92, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(403 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (405 : Vertex) [(403 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 27 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value27, value87, value88, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (147 : Vertex) (401 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 27 = false ∨ valuation q 87 = false ∨ valuation q 94 = false := by
  rw [value27, value87, value88, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (147 : Vertex) (401 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 27 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value27, value88, value91, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (147 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 87 = false ∨ valuation q 94 = false ∨ valuation q 110 = false := by
  rw [value87, value88, value94, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (401 : Vertex) (411 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 110 = false := by
  rw [value88, value91, value94, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (407 : Vertex) (411 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 28 = false ∨ valuation q 78 = false ∨ valuation q 90 = false := by
  rw [value28, value78, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (404 : Vertex) (148 : Vertex) (388 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 78 = false ∨ valuation q 90 = false ∨ valuation q 111 = false := by
  rw [value78, value89, value90, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (404 : Vertex) (388 : Vertex) (405 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 208 = true ∨ valuation q 89 = true ∨ valuation q 91 = true := by
  rw [value89, value90, value91, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(404 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (401 : Vertex) [(404 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 208 = true ∨ valuation q 87 = true ∨ valuation q 91 = true := by
  rw [value87, value90, value91, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(401 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (404 : Vertex) [(401 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 208 = true ∨ valuation q 87 = true ∨ valuation q 89 = true := by
  rw [value87, value89, value90, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(401 : Vertex), (404 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (407 : Vertex) [(401 : Vertex), (404 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 80 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value80, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (403 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 80 = false ∨ valuation q 88 = false ∨ valuation q 113 = false := by
  rw [value80, value88, value91, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (403 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 80 = false ∨ valuation q 90 = false ∨ valuation q 113 = false := by
  rw [value80, value90, value91, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (405 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 113 = false := by
  rw [value88, value90, value91, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (403 : Vertex) (405 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 209 = true ∨ valuation q 80 = true ∨ valuation q 88 = true ∨ valuation q 113 = true := by
  rw [value80, value88, value91, value113, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(391 : Vertex), (403 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (405 : Vertex) [(391 : Vertex), (403 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 82 = false ∨ valuation q 87 = false ∨ valuation q 94 = false := by
  rw [value82, value87, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (401 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 210 = true ∨ valuation q 87 = true ∨ valuation q 94 = true := by
  rw [value87, value92, value94, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(401 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (393 : Vertex) [(401 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 210 = true ∨ valuation q 82 = true ∨ valuation q 94 = true := by
  rw [value82, value92, value94, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(393 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (401 : Vertex) [(393 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 210 = true ∨ valuation q 82 = true ∨ valuation q 87 = true := by
  rw [value82, value87, value92, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(393 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (411 : Vertex) [(393 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 94 = true ∨ valuation q 95 = true := by
  rw [value93, value94, value95, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(411 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (394 : Vertex) [(411 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 83 = true ∨ valuation q 95 = true := by
  rw [value83, value93, value95, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(394 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (411 : Vertex) [(394 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 83 = true ∨ valuation q 94 = true := by
  rw [value83, value93, value94, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(394 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (414 : Vertex) [(394 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 88 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value88, value92, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (403 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 88 = true ∨ valuation q 92 = true := by
  rw [value88, value92, value94, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(403 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (410 : Vertex) [(403 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 86 = false ∨ valuation q 93 = false ∨ valuation q 117 = false := by
  rw [value86, value93, value95, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (410 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 33 = false ∨ valuation q 59 = false ∨ valuation q 108 = false := by
  rw [value33, value59, value96, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (320 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E096.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112096
