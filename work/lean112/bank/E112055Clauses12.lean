import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 193 = true ∨ valuation q 37 = true ∨ valuation q 62 = true := by
  rw [value37, value62, value65, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(94 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (158 : Vertex) [(94 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 193 = true ∨ valuation q 37 = true ∨ valuation q 55 = true := by
  rw [value37, value55, value65, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(94 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (206 : Vertex) [(94 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 194 = true := by
  rw [value66, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (228 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (228 : Vertex) (229 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 195 = true ∨ valuation q 59 = true ∨ valuation q 66 = true ∨ valuation q 68 = true := by
  rw [value59, value66, value67, value68, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(197 : Vertex), (228 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (485 : Vertex) [(197 : Vertex), (228 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 196 = true := by
  rw [value68, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (245 : Vertex) (229 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 69 = true := by
  rw [value69, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (259 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 73 = true ∨ valuation q 76 = true := by
  rw [value69, value73, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ∈ [(263 : Vertex), (267 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (259 : Vertex) [(263 : Vertex), (267 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 73 = false ∨ valuation q 76 = false := by
  rw [value73, value76, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (259 : Vertex) (263 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 197 = true ∨ valuation q 76 = true := by
  rw [value69, value76, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(267 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (263 : Vertex) [(267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 197 = true ∨ valuation q 73 = true := by
  rw [value69, value73, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(263 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (267 : Vertex) [(263 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 77 = false := by
  rw [value70, value71, value72, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (262 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 82 = false := by
  rw [value70, value71, value72, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (262 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 77 = false ∨ valuation q 82 = false := by
  rw [value70, value71, value77, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (268 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 77 = false ∨ valuation q 82 = false := by
  rw [value70, value72, value77, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (262 : Vertex) (268 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 198 = true ∨ valuation q 72 = true ∨ valuation q 77 = true ∨ valuation q 82 = true := by
  rw [value70, value72, value77, value82, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(262 : Vertex), (268 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (261 : Vertex) [(262 : Vertex), (268 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 198 = true ∨ valuation q 71 = true ∨ valuation q 77 = true ∨ valuation q 82 = true := by
  rw [value70, value71, value77, value82, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(261 : Vertex), (268 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (262 : Vertex) [(261 : Vertex), (268 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 198 = true ∨ valuation q 71 = true ∨ valuation q 72 = true ∨ valuation q 82 = true := by
  rw [value70, value71, value72, value82, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (268 : Vertex) [(261 : Vertex), (262 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 198 = true ∨ valuation q 71 = true ∨ valuation q 72 = true ∨ valuation q 77 = true := by
  rw [value70, value71, value72, value77, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex), (268 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (276 : Vertex) [(261 : Vertex), (262 : Vertex), (268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 4 = false ∨ valuation q 70 = false ∨ valuation q 78 = false := by
  rw [value4, value70, value71, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (5 : Vertex) (260 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 4 = false ∨ valuation q 70 = false ∨ valuation q 95 = false := by
  rw [value4, value70, value71, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (5 : Vertex) (260 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 4 = false ∨ valuation q 73 = false ∨ valuation q 78 = false := by
  rw [value4, value71, value73, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (5 : Vertex) (263 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 4 = false ∨ valuation q 73 = false ∨ valuation q 95 = false := by
  rw [value4, value71, value73, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (5 : Vertex) (263 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 4 = false ∨ valuation q 83 = false ∨ valuation q 95 = false := by
  rw [value4, value71, value83, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (5 : Vertex) (277 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 78 = false := by
  rw [value70, value71, value73, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (260 : Vertex) (263 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 95 = false := by
  rw [value70, value71, value73, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (260 : Vertex) (263 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 70 = false ∨ valuation q 78 = false ∨ valuation q 95 = false := by
  rw [value70, value71, value78, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (260 : Vertex) (269 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 70 = false ∨ valuation q 95 = false ∨ valuation q 112 = false := by
  rw [value70, value71, value95, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (260 : Vertex) (325 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 73 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value71, value73, value78, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (263 : Vertex) (269 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 73 = false ∨ valuation q 78 = false ∨ valuation q 95 = false := by
  rw [value71, value73, value78, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (263 : Vertex) (269 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 73 = false ∨ valuation q 83 = false ∨ valuation q 95 = false := by
  rw [value71, value73, value83, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (263 : Vertex) (277 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 73 = false ∨ valuation q 95 = false ∨ valuation q 112 = false := by
  rw [value71, value73, value95, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (263 : Vertex) (325 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 78 = false ∨ valuation q 95 = false ∨ valuation q 112 = false := by
  rw [value71, value78, value95, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (269 : Vertex) (325 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E055.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112055
