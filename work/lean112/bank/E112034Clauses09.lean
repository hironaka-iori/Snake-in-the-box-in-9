import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 63 = false ∨ valuation q 66 = false ∨ valuation q 105 = false := by
  rw [value63, value66, value68, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (319 : Vertex) (311 : Vertex) (315 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 63 = false ∨ valuation q 67 = false ∨ valuation q 85 = false := by
  rw [value63, value67, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (319 : Vertex) (311 : Vertex) (317 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 63 = false ∨ valuation q 67 = false ∨ valuation q 105 = false := by
  rw [value63, value67, value68, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (319 : Vertex) (311 : Vertex) (317 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 85 = false := by
  rw [value66, value67, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (319 : Vertex) (315 : Vertex) (317 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 52 = false ∨ valuation q 70 = false ∨ valuation q 74 = false := by
  rw [value52, value69, value70, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (354 : Vertex) (290 : Vertex) (355 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 52 = false ∨ valuation q 70 = false ∨ valuation q 107 = false := by
  rw [value52, value69, value70, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (354 : Vertex) (290 : Vertex) (355 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 52 = false ∨ valuation q 74 = false ∨ valuation q 107 = false := by
  rw [value52, value69, value74, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (354 : Vertex) (290 : Vertex) (362 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 107 = false := by
  rw [value69, value70, value74, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (354 : Vertex) (355 : Vertex) (362 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 52 = false ∨ valuation q 70 = false := by
  rw [value52, value70, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (354 : Vertex) (290 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 52 = false ∨ valuation q 74 = false := by
  rw [value52, value74, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (354 : Vertex) (290 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 197 = true ∨ valuation q 70 = true ∨ valuation q 74 = true ∨ valuation q 107 = true := by
  rw [value69, value70, value74, value107, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (354 : Vertex) w → w ∈ region → w ≠ (290 : Vertex) → w ∈ [(355 : Vertex), (362 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (354 : Vertex) (290 : Vertex) [(355 : Vertex), (362 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 197 = true ∨ valuation q 52 = true ∨ valuation q 70 = true ∨ valuation q 107 = true := by
  rw [value52, value69, value70, value107, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (354 : Vertex) w → w ∈ region → w ≠ (362 : Vertex) → w ∈ [(290 : Vertex), (355 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (354 : Vertex) (362 : Vertex) [(290 : Vertex), (355 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 75 = false ∨ valuation q 80 = false := by
  rw [value69, value70, value75, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (354 : Vertex) (363 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 75 = false ∨ valuation q 108 = false := by
  rw [value69, value70, value75, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (354 : Vertex) (363 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 80 = false ∨ valuation q 108 = false := by
  rw [value69, value70, value80, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (354 : Vertex) (371 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 75 = false ∨ valuation q 80 = false ∨ valuation q 108 = false := by
  rw [value70, value75, value80, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (363 : Vertex) (371 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 198 = true ∨ valuation q 75 = true ∨ valuation q 80 = true ∨ valuation q 108 = true := by
  rw [value70, value75, value80, value108, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (354 : Vertex) → w ∈ [(363 : Vertex), (371 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (354 : Vertex) [(363 : Vertex), (371 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 198 = true ∨ valuation q 69 = true ∨ valuation q 80 = true ∨ valuation q 108 = true := by
  rw [value69, value70, value80, value108, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(354 : Vertex), (371 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (363 : Vertex) [(354 : Vertex), (371 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 198 = true ∨ valuation q 69 = true ∨ valuation q 75 = true ∨ valuation q 108 = true := by
  rw [value69, value70, value75, value108, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (371 : Vertex) → w ∈ [(354 : Vertex), (363 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (371 : Vertex) [(354 : Vertex), (363 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 53 = false ∨ valuation q 72 = false ∨ valuation q 81 = false := by
  rw [value53, value71, value72, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (292 : Vertex) (357 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 53 = false ∨ valuation q 72 = false ∨ valuation q 109 = false := by
  rw [value53, value71, value72, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (292 : Vertex) (357 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 81 = false ∨ valuation q 109 = false := by
  rw [value71, value72, value81, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (357 : Vertex) (372 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 54 = false ∨ valuation q 71 = false ∨ valuation q 76 = false := by
  rw [value54, value71, value72, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (293 : Vertex) (356 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 54 = false ∨ valuation q 76 = false ∨ valuation q 110 = false := by
  rw [value54, value72, value76, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (293 : Vertex) (365 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 71 = false ∨ valuation q 76 = false ∨ valuation q 110 = false := by
  rw [value71, value72, value76, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (356 : Vertex) (365 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 71 = true ∨ valuation q 76 = true ∨ valuation q 110 = true := by
  rw [value71, value72, value76, value110, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (293 : Vertex) → w ∈ [(356 : Vertex), (365 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (293 : Vertex) [(356 : Vertex), (365 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 54 = true ∨ valuation q 76 = true ∨ valuation q 110 = true := by
  rw [value54, value72, value76, value110, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(293 : Vertex), (365 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (356 : Vertex) [(293 : Vertex), (365 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 54 = true ∨ valuation q 71 = true ∨ valuation q 110 = true := by
  rw [value54, value71, value72, value110, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (365 : Vertex) → w ∈ [(293 : Vertex), (356 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (365 : Vertex) [(293 : Vertex), (356 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 54 = true ∨ valuation q 71 = true ∨ valuation q 76 = true := by
  rw [value54, value71, value72, value76, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(293 : Vertex), (356 : Vertex), (365 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (485 : Vertex) [(293 : Vertex), (356 : Vertex), (365 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 201 = true ∨ valuation q 76 = true ∨ valuation q 114 = true := by
  rw [value73, value76, value114, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(365 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (363 : Vertex) [(365 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 201 = true ∨ valuation q 75 = true ∨ valuation q 114 = true := by
  rw [value73, value75, value114, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (365 : Vertex) → w ∈ [(363 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (365 : Vertex) [(363 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 201 = true ∨ valuation q 75 = true ∨ valuation q 76 = true := by
  rw [value73, value75, value76, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(363 : Vertex), (365 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (489 : Vertex) [(363 : Vertex), (365 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block9 (q : Snake 81) (h : Conditions q) : B112E034.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112034
