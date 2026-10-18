import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 183 = true ∨ valuation q 48 = true ∨ valuation q 68 = true ∨ valuation q 71 = true := by
  rw [value48, value66, value68, value71, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(146 : Vertex), (214 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (82 : Vertex) [(146 : Vertex), (214 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 183 = true ∨ valuation q 29 = true ∨ valuation q 68 = true ∨ valuation q 71 = true := by
  rw [value29, value66, value68, value71, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(82 : Vertex), (214 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (146 : Vertex) [(82 : Vertex), (214 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 183 = true ∨ valuation q 29 = true ∨ valuation q 48 = true ∨ valuation q 71 = true := by
  rw [value29, value48, value66, value71, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(82 : Vertex), (146 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (214 : Vertex) [(82 : Vertex), (146 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 183 = true ∨ valuation q 29 = true ∨ valuation q 48 = true ∨ valuation q 68 = true := by
  rw [value29, value48, value66, value68, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(82 : Vertex), (146 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (218 : Vertex) [(82 : Vertex), (146 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 59 = false ∨ valuation q 66 = false ∨ valuation q 69 = false := by
  rw [value59, value66, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (214 : Vertex) (198 : Vertex) (210 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 60 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value60, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (199 : Vertex) (213 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 186 = true ∨ valuation q 67 = true ∨ valuation q 68 = true := by
  rw [value67, value68, value69, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(213 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (199 : Vertex) [(213 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 186 = true ∨ valuation q 60 = true ∨ valuation q 68 = true := by
  rw [value60, value68, value69, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(199 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (213 : Vertex) [(199 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 186 = true ∨ valuation q 60 = true ∨ valuation q 67 = true := by
  rw [value60, value67, value69, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(199 : Vertex), (213 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (214 : Vertex) [(199 : Vertex), (213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 62 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value62, value70, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (201 : Vertex) (219 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 33 = false ∨ valuation q 51 = false ∨ valuation q 66 = false := by
  rw [value33, value51, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (154 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 33 = false ∨ valuation q 51 = false ∨ valuation q 72 = false := by
  rw [value33, value51, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (154 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 33 = false ∨ valuation q 66 = false ∨ valuation q 72 = false := by
  rw [value33, value66, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (210 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 51 = false ∨ valuation q 66 = false ∨ valuation q 72 = false := by
  rw [value51, value66, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (210 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 34 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value34, value70, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (91 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 63 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value63, value70, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (203 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 189 = true ∨ valuation q 63 = true ∨ valuation q 70 = true ∨ valuation q 71 = true := by
  rw [value63, value70, value71, value72, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(203 : Vertex), (217 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (91 : Vertex) [(203 : Vertex), (217 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 189 = true ∨ valuation q 34 = true ∨ valuation q 70 = true ∨ valuation q 71 = true := by
  rw [value34, value70, value71, value72, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(91 : Vertex), (217 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (203 : Vertex) [(91 : Vertex), (217 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 189 = true ∨ valuation q 34 = true ∨ valuation q 63 = true ∨ valuation q 71 = true := by
  rw [value34, value63, value71, value72, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(91 : Vertex), (203 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (217 : Vertex) [(91 : Vertex), (203 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 189 = true ∨ valuation q 34 = true ∨ valuation q 63 = true ∨ valuation q 70 = true := by
  rw [value34, value63, value70, value72, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(91 : Vertex), (203 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (218 : Vertex) [(91 : Vertex), (203 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 53 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value53, value67, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (157 : Vertex) (213 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 190 = true ∨ valuation q 53 = true ∨ valuation q 70 = true := by
  rw [value53, value70, value73, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(157 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (213 : Vertex) [(157 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 190 = true ∨ valuation q 53 = true ∨ valuation q 67 = true := by
  rw [value53, value67, value73, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(157 : Vertex), (213 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (217 : Vertex) [(157 : Vertex), (213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 15 = true ∨ valuation q 75 = true ∨ valuation q 78 = true := by
  rw [value15, value74, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ∈ [(64 : Vertex), (321 : Vertex), (328 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (320 : Vertex) [(64 : Vertex), (321 : Vertex), (328 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 191 = true ∨ valuation q 75 = true ∨ valuation q 78 = true := by
  rw [value74, value75, value78, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (64 : Vertex) → w ∈ [(321 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (64 : Vertex) [(321 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 191 = true ∨ valuation q 15 = true ∨ valuation q 78 = true := by
  rw [value15, value74, value78, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(64 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (321 : Vertex) [(64 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 191 = true ∨ valuation q 15 = true ∨ valuation q 75 = true := by
  rw [value15, value74, value75, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(64 : Vertex), (321 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (328 : Vertex) [(64 : Vertex), (321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 16 = false ∨ valuation q 74 = false ∨ valuation q 79 = false := by
  rw [value16, value74, value75, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (65 : Vertex) (320 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 192 = true ∨ valuation q 16 = true ∨ valuation q 79 = true := by
  rw [value16, value75, value79, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(65 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(65 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 193 = true ∨ valuation q 82 = true ∨ valuation q 86 = true := by
  rw [value76, value82, value86, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(334 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (327 : Vertex) [(334 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 193 = true ∨ valuation q 77 = true ∨ valuation q 86 = true := by
  rw [value76, value77, value86, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(327 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (334 : Vertex) [(327 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 20 = false ∨ valuation q 76 = false ∨ valuation q 87 = false := by
  rw [value20, value76, value77, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (71 : Vertex) (326 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E213.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112213
