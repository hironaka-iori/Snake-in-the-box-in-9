import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 58 = true ∨ valuation q 62 = true ∨ valuation q 118 = true := by
  rw [value58, value60, value62, value118, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(209 : Vertex), (215 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (197 : Vertex) [(209 : Vertex), (215 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 50 = true ∨ valuation q 62 = true ∨ valuation q 118 = true := by
  rw [value50, value60, value62, value118, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(197 : Vertex), (215 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (209 : Vertex) [(197 : Vertex), (215 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 50 = true ∨ valuation q 58 = true ∨ valuation q 118 = true := by
  rw [value50, value58, value60, value118, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(197 : Vertex), (209 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (215 : Vertex) [(197 : Vertex), (209 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 50 = true ∨ valuation q 58 = true ∨ valuation q 62 = true := by
  rw [value50, value58, value60, value62, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(197 : Vertex), (209 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (469 : Vertex) [(197 : Vertex), (209 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 42 = true ∨ valuation q 51 = true ∨ valuation q 62 = true ∨ valuation q 119 = true := by
  rw [value42, value51, value61, value62, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ∈ [(150 : Vertex), (198 : Vertex), (215 : Vertex), (470 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (214 : Vertex) [(150 : Vertex), (198 : Vertex), (215 : Vertex), (470 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 51 = true ∨ valuation q 62 = true ∨ valuation q 119 = true := by
  rw [value51, value61, value62, value119, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(198 : Vertex), (215 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (150 : Vertex) [(198 : Vertex), (215 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 42 = true ∨ valuation q 62 = true ∨ valuation q 119 = true := by
  rw [value42, value61, value62, value119, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(150 : Vertex), (215 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (198 : Vertex) [(150 : Vertex), (215 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 42 = true ∨ valuation q 51 = true ∨ valuation q 119 = true := by
  rw [value42, value51, value61, value119, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(150 : Vertex), (198 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (215 : Vertex) [(150 : Vertex), (198 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 42 = true ∨ valuation q 51 = true ∨ valuation q 62 = true := by
  rw [value42, value51, value61, value62, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(150 : Vertex), (198 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (470 : Vertex) [(150 : Vertex), (198 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value59, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (211 : Vertex) (213 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 60 = true ∨ valuation q 61 = true := by
  rw [value60, value61, value62, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(213 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (211 : Vertex) [(213 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 59 = true ∨ valuation q 61 = true := by
  rw [value59, value61, value62, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(211 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (213 : Vertex) [(211 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 59 = true ∨ valuation q 60 = true := by
  rw [value59, value60, value62, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(211 : Vertex), (213 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (214 : Vertex) [(211 : Vertex), (213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 52 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value52, value63, value64, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (200 : Vertex) (217 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 187 = true ∨ valuation q 64 = true ∨ valuation q 66 = true := by
  rw [value63, value64, value66, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(217 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (200 : Vertex) [(217 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 187 = true ∨ valuation q 52 = true ∨ valuation q 66 = true := by
  rw [value52, value63, value66, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(200 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (217 : Vertex) [(200 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 187 = true ∨ valuation q 52 = true ∨ valuation q 64 = true := by
  rw [value52, value63, value64, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(200 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (220 : Vertex) [(200 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 64 = true := by
  rw [value64, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (217 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 58 = true ∨ valuation q 63 = true ∨ valuation q 65 = true := by
  rw [value58, value63, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ∈ [(209 : Vertex), (216 : Vertex), (219 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (217 : Vertex) [(209 : Vertex), (216 : Vertex), (219 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value63, value65, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (217 : Vertex) (216 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 188 = true ∨ valuation q 63 = true ∨ valuation q 65 = true := by
  rw [value63, value64, value65, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(216 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (209 : Vertex) [(216 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 188 = true ∨ valuation q 58 = true ∨ valuation q 65 = true := by
  rw [value58, value64, value65, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(209 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (216 : Vertex) [(209 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 188 = true ∨ valuation q 58 = true ∨ valuation q 63 = true := by
  rw [value58, value63, value64, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(209 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (219 : Vertex) [(209 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 54 = false ∨ valuation q 59 = false ∨ valuation q 64 = false := by
  rw [value54, value59, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (203 : Vertex) (211 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 59 = true ∨ valuation q 64 = true := by
  rw [value59, value64, value65, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(211 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (203 : Vertex) [(211 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 54 = true ∨ valuation q 64 = true := by
  rw [value54, value64, value65, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(203 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (211 : Vertex) [(203 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 54 = true ∨ valuation q 59 = true := by
  rw [value54, value59, value65, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(203 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (217 : Vertex) [(203 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 66 = true := by
  rw [value66, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (220 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 55 = true ∨ valuation q 63 = true ∨ valuation q 121 = true := by
  rw [value55, value63, value66, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ∈ [(204 : Vertex), (216 : Vertex), (476 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (220 : Vertex) [(204 : Vertex), (216 : Vertex), (476 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 55 = false ∨ valuation q 63 = false ∨ valuation q 121 = false := by
  rw [value55, value63, value66, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (220 : Vertex) (204 : Vertex) (216 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 55 = false ∨ valuation q 63 = false := by
  rw [value55, value63, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (220 : Vertex) (204 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 63 = false ∨ valuation q 121 = false := by
  rw [value63, value121, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (220 : Vertex) (216 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E105.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112105
