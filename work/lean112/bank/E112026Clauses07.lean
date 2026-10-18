import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 50 = false ∨ valuation q 60 = false ∨ valuation q 94 = false := by
  rw [value50, value58, value60, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (289 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 60 = false ∨ valuation q 94 = false := by
  rw [value57, value58, value60, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (304 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 179 = true ∨ valuation q 57 = true ∨ valuation q 60 = true ∨ valuation q 94 = true := by
  rw [value57, value58, value60, value94, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(304 : Vertex), (307 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (289 : Vertex) [(304 : Vertex), (307 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 179 = true ∨ valuation q 50 = true ∨ valuation q 60 = true ∨ valuation q 94 = true := by
  rw [value50, value58, value60, value94, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (304 : Vertex) → w ∈ [(289 : Vertex), (307 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (304 : Vertex) [(289 : Vertex), (307 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 57 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value57, value59, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (304 : Vertex) (307 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 180 = true ∨ valuation q 57 = true ∨ valuation q 62 = true := by
  rw [value57, value59, value62, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (306 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(304 : Vertex), (310 : Vertex)] := by decide
  have hg := other_cover q (306 : Vertex) (307 : Vertex) [(304 : Vertex), (310 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 95 = false := by
  rw [value58, value59, value60, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (305 : Vertex) (306 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 181 = true ∨ valuation q 59 = true ∨ valuation q 95 = true := by
  rw [value59, value60, value95, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(306 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(306 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 181 = true ∨ valuation q 58 = true ∨ valuation q 95 = true := by
  rw [value58, value60, value95, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(305 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (306 : Vertex) [(305 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 181 = true ∨ valuation q 58 = true ∨ valuation q 59 = true := by
  rw [value58, value59, value60, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(305 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (435 : Vertex) [(305 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 6 = false ∨ valuation q 57 = false ∨ valuation q 63 = false := by
  rw [value6, value57, value61, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (52 : Vertex) (304 : Vertex) (316 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 6 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value6, value61, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (52 : Vertex) (310 : Vertex) (316 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 6 = false ∨ valuation q 62 = false ∨ valuation q 96 = false := by
  rw [value6, value61, value62, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (52 : Vertex) (310 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 57 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value57, value61, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (304 : Vertex) (310 : Vertex) (316 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 57 = false ∨ valuation q 62 = false ∨ valuation q 96 = false := by
  rw [value57, value61, value62, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (304 : Vertex) (310 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 57 = false ∨ valuation q 63 = false ∨ valuation q 96 = false := by
  rw [value57, value61, value63, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (304 : Vertex) (316 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 57 = false ∨ valuation q 74 = false ∨ valuation q 96 = false := by
  rw [value57, value61, value74, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (304 : Vertex) (372 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 74 = false := by
  rw [value61, value62, value63, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (310 : Vertex) (316 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 96 = false := by
  rw [value61, value62, value63, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (310 : Vertex) (316 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 74 = false ∨ valuation q 96 = false := by
  rw [value61, value62, value74, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (310 : Vertex) (372 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 74 = false ∨ valuation q 96 = false := by
  rw [value61, value63, value74, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (316 : Vertex) (372 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 51 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value51, value59, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (310 : Vertex) (294 : Vertex) (306 : Vertex) (308 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 51 = false ∨ valuation q 59 = false ∨ valuation q 65 = false := by
  rw [value51, value59, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (310 : Vertex) (294 : Vertex) (306 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 183 = true ∨ valuation q 59 = true ∨ valuation q 61 = true ∨ valuation q 65 = true := by
  rw [value59, value61, value62, value65, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(306 : Vertex), (308 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (294 : Vertex) [(306 : Vertex), (308 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 183 = true ∨ valuation q 51 = true ∨ valuation q 59 = true ∨ valuation q 61 = true := by
  rw [value51, value59, value61, value62, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(294 : Vertex), (306 : Vertex), (308 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (318 : Vertex) [(294 : Vertex), (306 : Vertex), (308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 184 = true ∨ valuation q 64 = true ∨ valuation q 65 = true := by
  rw [value63, value64, value65, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(317 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (308 : Vertex) [(317 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 184 = true ∨ valuation q 61 = true ∨ valuation q 65 = true := by
  rw [value61, value63, value65, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(308 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (317 : Vertex) [(308 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 184 = true ∨ valuation q 61 = true ∨ valuation q 64 = true := by
  rw [value61, value63, value64, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(308 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (318 : Vertex) [(308 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 185 = true ∨ valuation q 55 = true := by
  rw [value55, value64, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (316 : Vertex) → w ∈ [(301 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (316 : Vertex) [(301 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 186 = true ∨ valuation q 63 = true := by
  rw [value63, value65, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (318 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(316 : Vertex)] := by decide
  have hg := other_cover q (318 : Vertex) (310 : Vertex) [(316 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 186 = true ∨ valuation q 62 = true := by
  rw [value62, value65, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (318 : Vertex) w → w ∈ region → w ≠ (316 : Vertex) → w ∈ [(310 : Vertex)] := by decide
  have hg := other_cover q (318 : Vertex) (316 : Vertex) [(310 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 188 = true ∨ valuation q 9 = true ∨ valuation q 71 = true := by
  rw [value9, value67, value71, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (354 : Vertex) → w ∈ [(99 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (354 : Vertex) [(99 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E026.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112026
