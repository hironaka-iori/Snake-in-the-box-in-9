import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 206 = true ∨ valuation q 91 = true ∨ valuation q 94 = true := by
  rw [value91, value94, value95, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(407 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (411 : Vertex) [(407 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 206 = true ∨ valuation q 91 = true ∨ valuation q 92 = true := by
  rw [value91, value92, value95, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(407 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (414 : Vertex) [(407 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 104 = false := by
  rw [value96, value97, value98, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (482 : Vertex) (484 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 207 = true ∨ valuation q 98 = true ∨ valuation q 104 = true := by
  rw [value96, value98, value104, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [(484 : Vertex), (496 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (482 : Vertex) [(484 : Vertex), (496 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 207 = true ∨ valuation q 97 = true ∨ valuation q 98 = true := by
  rw [value96, value97, value98, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (496 : Vertex) → w ∈ [(482 : Vertex), (484 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (496 : Vertex) [(482 : Vertex), (484 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 208 = true ∨ valuation q 100 = true := by
  rw [value97, value100, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(490 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (480 : Vertex) [(490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 208 = true ∨ valuation q 96 = true := by
  rw [value96, value97, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(480 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (490 : Vertex) [(480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 209 = true ∨ valuation q 96 = true ∨ valuation q 102 = true := by
  rw [value96, value98, value102, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (484 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(480 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (484 : Vertex) (485 : Vertex) [(480 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 209 = true ∨ valuation q 96 = true ∨ valuation q 99 = true := by
  rw [value96, value98, value99, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (484 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(480 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (484 : Vertex) (492 : Vertex) [(480 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 40 = false ∨ valuation q 98 = false ∨ valuation q 103 = false := by
  rw [value40, value98, value99, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (229 : Vertex) (484 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 210 = true ∨ valuation q 98 = true ∨ valuation q 103 = true := by
  rw [value98, value99, value103, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (485 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(484 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (485 : Vertex) (229 : Vertex) [(484 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 211 = true ∨ valuation q 101 = true := by
  rw [value100, value101, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [(491 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (482 : Vertex) [(491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 211 = true ∨ valuation q 97 = true := by
  rw [value97, value100, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (491 : Vertex) → w ∈ [(482 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (491 : Vertex) [(482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 212 = true ∨ valuation q 100 = true ∨ valuation q 108 = true := by
  rw [value100, value101, value108, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(490 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (235 : Vertex) [(490 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 212 = true ∨ valuation q 41 = true ∨ valuation q 108 = true := by
  rw [value41, value101, value108, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(235 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (490 : Vertex) [(235 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 212 = true ∨ valuation q 41 = true ∨ valuation q 100 = true := by
  rw [value41, value100, value101, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(235 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (507 : Vertex) [(235 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 98 = false ∨ valuation q 103 = false ∨ valuation q 109 = false := by
  rw [value98, value102, value103, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (484 : Vertex) (493 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 213 = true ∨ valuation q 98 = true ∨ valuation q 109 = true := by
  rw [value98, value102, value109, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(484 : Vertex), (508 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (493 : Vertex) [(484 : Vertex), (508 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 99 = true ∨ valuation q 102 = true := by
  rw [value99, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ∈ [(485 : Vertex), (492 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (493 : Vertex) [(485 : Vertex), (492 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 214 = true ∨ valuation q 102 = true := by
  rw [value102, value103, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(492 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (485 : Vertex) [(492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 214 = true ∨ valuation q 99 = true := by
  rw [value99, value103, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(485 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (492 : Vertex) [(485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 215 = true ∨ valuation q 105 = true := by
  rw [value104, value105, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(497 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (480 : Vertex) [(497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 215 = true ∨ valuation q 96 = true := by
  rw [value96, value104, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(480 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (497 : Vertex) [(480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 216 = true ∨ valuation q 106 = true := by
  rw [value105, value106, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (496 : Vertex) → w ∈ [(499 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (496 : Vertex) [(499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 216 = true ∨ valuation q 104 = true := by
  rw [value104, value105, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(496 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (499 : Vertex) [(496 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 217 = true ∨ valuation q 105 = true ∨ valuation q 108 = true := by
  rw [value105, value106, value108, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(497 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (503 : Vertex) [(497 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 217 = true ∨ valuation q 105 = true ∨ valuation q 107 = true := by
  rw [value105, value106, value107, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(497 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (507 : Vertex) [(497 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 218 = true ∨ valuation q 106 = true := by
  rw [value106, value107, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (511 : Vertex) → w ∈ [(499 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (511 : Vertex) [(499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 101 = false ∨ valuation q 106 = false ∨ valuation q 111 = false := by
  rw [value101, value106, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (491 : Vertex) (499 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 219 = true ∨ valuation q 101 = true ∨ valuation q 106 = true := by
  rw [value101, value106, value108, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (507 : Vertex) w → w ∈ region → w ≠ (511 : Vertex) → w ∈ [(491 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (507 : Vertex) (511 : Vertex) [(491 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 109 = true := by
  rw [value109, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (508 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 220 = true ∨ valuation q 110 = true := by
  rw [value109, value110, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (492 : Vertex) [(510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block12 (q : Snake 81) (h : Conditions q) : B112E161.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112161
