import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 50 = false ∨ valuation q 86 = false ∨ valuation q 96 = false := by
  rw [value50, value84, value86, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (398 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 50 = false ∨ valuation q 96 = false ∨ valuation q 106 = false := by
  rw [value50, value84, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 96 = false := by
  rw [value84, value85, value86, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (397 : Vertex) (398 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 106 = false := by
  rw [value84, value85, value86, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (397 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 96 = false ∨ valuation q 106 = false := by
  rw [value84, value85, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (397 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 96 = false ∨ valuation q 106 = false := by
  rw [value84, value86, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (398 : Vertex) (412 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value80, value82, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (389 : Vertex) (393 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 201 = true ∨ valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 87 = true ∨ valuation q 97 = true := by
  rw [value82, value84, value85, value87, value97, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(393 : Vertex), (396 : Vertex), (399 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (389 : Vertex) [(393 : Vertex), (396 : Vertex), (399 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 201 = true ∨ valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 97 = true := by
  rw [value80, value82, value84, value85, value97, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(389 : Vertex), (393 : Vertex), (396 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (399 : Vertex) [(389 : Vertex), (393 : Vertex), (396 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 201 = true ∨ valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 87 = true := by
  rw [value80, value82, value84, value85, value87, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(389 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (413 : Vertex) [(389 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value81, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (391 : Vertex) (397 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 77 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value77, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (385 : Vertex) (400 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 77 = false ∨ valuation q 88 = false ∨ valuation q 94 = false := by
  rw [value77, value88, value89, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (385 : Vertex) (400 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 77 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value77, value89, value91, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (385 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value88, value89, value91, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (400 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 78 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value78, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (400 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 78 = false ∨ valuation q 88 = false ∨ valuation q 92 = false := by
  rw [value78, value88, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (400 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 78 = false ∨ valuation q 88 = false ∨ valuation q 95 = false := by
  rw [value78, value88, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (400 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 78 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value78, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (403 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 78 = false ∨ valuation q 91 = false ∨ valuation q 95 = false := by
  rw [value78, value90, value91, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (403 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 78 = false ∨ valuation q 92 = false ∨ valuation q 95 = false := by
  rw [value78, value90, value92, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value88, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (400 : Vertex) (403 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 95 = false := by
  rw [value88, value90, value91, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (400 : Vertex) (403 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 88 = false ∨ valuation q 92 = false ∨ valuation q 95 = false := by
  rw [value88, value90, value92, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (400 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 95 = false := by
  rw [value90, value91, value92, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (403 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 92 = false ∨ valuation q 95 = false := by
  rw [value92, value95, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (402 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 206 = true ∨ valuation q 78 = true ∨ valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 95 = true := by
  rw [value78, value88, value90, value91, value95, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(386 : Vertex), (400 : Vertex), (403 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (406 : Vertex) [(386 : Vertex), (400 : Vertex), (403 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 207 = true ∨ valuation q 89 = true ∨ valuation q 90 = true := by
  rw [value89, value90, value91, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(401 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (387 : Vertex) [(401 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 207 = true ∨ valuation q 79 = true ∨ valuation q 90 = true := by
  rw [value79, value90, value91, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(387 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (401 : Vertex) [(387 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 207 = true ∨ valuation q 79 = true ∨ valuation q 89 = true := by
  rw [value79, value89, value91, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(387 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (402 : Vertex) [(387 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 208 = true ∨ valuation q 98 = true ∨ valuation q 111 = true := by
  rw [value92, value98, value111, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(414 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (402 : Vertex) [(414 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 208 = true ∨ valuation q 90 = true ∨ valuation q 111 = true := by
  rw [value90, value92, value111, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(402 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (414 : Vertex) [(402 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E120.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112120
