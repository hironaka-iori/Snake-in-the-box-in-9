import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 176 = true ∨ valuation q 58 = true ∨ valuation q 65 = true ∨ valuation q 68 = true := by
  rw [value58, value59, value65, value68, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(196 : Vertex), (206 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (199 : Vertex) [(196 : Vertex), (206 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 176 = true ∨ valuation q 58 = true ∨ valuation q 60 = true ∨ valuation q 65 = true := by
  rw [value58, value59, value60, value65, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(196 : Vertex), (199 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (214 : Vertex) [(196 : Vertex), (199 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 20 = false ∨ valuation q 42 = false ∨ valuation q 69 = false := by
  rw [value20, value42, value60, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (71 : Vertex) (135 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 20 = false ∨ valuation q 59 = false ∨ valuation q 69 = false := by
  rw [value20, value59, value60, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (71 : Vertex) (198 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 42 = false ∨ valuation q 59 = false ∨ valuation q 69 = false := by
  rw [value42, value59, value60, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (135 : Vertex) (198 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 21 = false ∨ valuation q 56 = false ∨ valuation q 62 = false := by
  rw [value21, value56, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (192 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 21 = false ∨ valuation q 56 = false ∨ valuation q 64 = false := by
  rw [value21, value56, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (192 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 21 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value21, value61, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (201 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 56 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value56, value61, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (192 : Vertex) (201 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 56 = false ∨ valuation q 64 = false := by
  rw [value56, value64, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (200 : Vertex) (192 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 178 = true ∨ valuation q 21 = true ∨ valuation q 62 = true ∨ valuation q 64 = true := by
  rw [value21, value61, value62, value64, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(72 : Vertex), (201 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (192 : Vertex) [(72 : Vertex), (201 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 43 = false ∨ valuation q 57 = false ∨ valuation q 70 = false := by
  rw [value43, value57, value62, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 43 = false ∨ valuation q 61 = false ∨ valuation q 63 = false := by
  rw [value43, value61, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 43 = false ∨ valuation q 61 = false ∨ valuation q 70 = false := by
  rw [value43, value61, value62, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 179 = true ∨ valuation q 57 = true ∨ valuation q 61 = true ∨ valuation q 63 = true ∨ valuation q 70 = true := by
  rw [value57, value61, value62, value63, value70, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(193 : Vertex), (200 : Vertex), (203 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (137 : Vertex) [(193 : Vertex), (200 : Vertex), (203 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 179 = true ∨ valuation q 43 = true ∨ valuation q 61 = true ∨ valuation q 63 = true ∨ valuation q 70 = true := by
  rw [value43, value61, value62, value63, value70, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(137 : Vertex), (200 : Vertex), (203 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (193 : Vertex) [(137 : Vertex), (200 : Vertex), (203 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 179 = true ∨ valuation q 43 = true ∨ valuation q 57 = true ∨ valuation q 61 = true ∨ valuation q 70 = true := by
  rw [value43, value57, value61, value62, value70, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(137 : Vertex), (193 : Vertex), (200 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (203 : Vertex) [(137 : Vertex), (193 : Vertex), (200 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 22 = false ∨ valuation q 62 = false ∨ valuation q 72 = false := by
  rw [value22, value62, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (75 : Vertex) (201 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 180 = true ∨ valuation q 22 = true ∨ valuation q 62 = true := by
  rw [value22, value62, value63, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(75 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (219 : Vertex) [(75 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 23 = false ∨ valuation q 58 = false ∨ valuation q 61 = false := by
  rw [value23, value58, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (196 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 23 = false ∨ valuation q 58 = false ∨ valuation q 65 = false := by
  rw [value23, value58, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (196 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 23 = false ∨ valuation q 61 = false ∨ valuation q 65 = false := by
  rw [value23, value61, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (200 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 181 = true ∨ valuation q 58 = true ∨ valuation q 61 = true ∨ valuation q 65 = true := by
  rw [value58, value61, value64, value65, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(196 : Vertex), (200 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (76 : Vertex) [(196 : Vertex), (200 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 181 = true ∨ valuation q 23 = true ∨ valuation q 61 = true ∨ valuation q 65 = true := by
  rw [value23, value61, value64, value65, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (196 : Vertex) → w ∈ [(76 : Vertex), (200 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (196 : Vertex) [(76 : Vertex), (200 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 181 = true ∨ valuation q 23 = true ∨ valuation q 58 = true ∨ valuation q 65 = true := by
  rw [value23, value58, value64, value65, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(76 : Vertex), (196 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (200 : Vertex) [(76 : Vertex), (196 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 181 = true ∨ valuation q 23 = true ∨ valuation q 58 = true ∨ valuation q 61 = true := by
  rw [value23, value58, value61, value64, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(76 : Vertex), (196 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (206 : Vertex) [(76 : Vertex), (196 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 25 = false ∨ valuation q 59 = false ∨ valuation q 64 = false := by
  rw [value25, value59, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (198 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 59 = false ∨ valuation q 64 = false := by
  rw [value59, value64, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (206 : Vertex) (198 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 182 = true ∨ valuation q 25 = true ∨ valuation q 59 = true := by
  rw [value25, value59, value65, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(78 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (204 : Vertex) [(78 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 29 = false ∨ valuation q 48 = false ∨ valuation q 68 = false := by
  rw [value29, value48, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (82 : Vertex) (146 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 29 = false ∨ valuation q 48 = false ∨ valuation q 71 = false := by
  rw [value29, value48, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (82 : Vertex) (146 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 29 = false ∨ valuation q 68 = false ∨ valuation q 71 = false := by
  rw [value29, value66, value68, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (82 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E213.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112213
