import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value79, value80, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (307 : Vertex) (310 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 208 = true ∨ valuation q 79 = true ∨ valuation q 102 = true := by
  rw [value79, value80, value102, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(306 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(306 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 208 = true ∨ valuation q 78 = true ∨ valuation q 102 = true := by
  rw [value78, value80, value102, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(305 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (306 : Vertex) [(305 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 208 = true ∨ valuation q 78 = true ∨ valuation q 79 = true := by
  rw [value78, value79, value80, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(305 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (435 : Vertex) [(305 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 11 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value11, value81, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (52 : Vertex) (310 : Vertex) (316 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 11 = false ∨ valuation q 84 = false ∨ valuation q 103 = false := by
  rw [value11, value81, value84, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (52 : Vertex) (316 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 84 = false ∨ valuation q 103 = false := by
  rw [value81, value82, value84, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (310 : Vertex) (316 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 71 = false ∨ valuation q 79 = false ∨ valuation q 81 = false := by
  rw [value71, value79, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (310 : Vertex) (294 : Vertex) (306 : Vertex) (308 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 71 = false ∨ valuation q 79 = false ∨ valuation q 86 = false := by
  rw [value71, value79, value82, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (310 : Vertex) (294 : Vertex) (306 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 210 = true ∨ valuation q 79 = true ∨ valuation q 81 = true ∨ valuation q 86 = true := by
  rw [value79, value81, value82, value86, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(306 : Vertex), (308 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (294 : Vertex) [(306 : Vertex), (308 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 210 = true ∨ valuation q 71 = true ∨ valuation q 79 = true ∨ valuation q 86 = true := by
  rw [value71, value79, value82, value86, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(294 : Vertex), (306 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (308 : Vertex) [(294 : Vertex), (306 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 211 = true ∨ valuation q 79 = true ∨ valuation q 86 = true ∨ valuation q 108 = true := by
  rw [value79, value83, value86, value108, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(306 : Vertex), (318 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (58 : Vertex) [(306 : Vertex), (318 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 211 = true ∨ valuation q 15 = true ∨ valuation q 86 = true ∨ valuation q 108 = true := by
  rw [value15, value83, value86, value108, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(58 : Vertex), (318 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (306 : Vertex) [(58 : Vertex), (318 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 211 = true ∨ valuation q 15 = true ∨ valuation q 79 = true ∨ valuation q 86 = true := by
  rw [value15, value79, value83, value86, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(58 : Vertex), (306 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (442 : Vertex) [(58 : Vertex), (306 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 212 = true ∨ valuation q 85 = true ∨ valuation q 86 = true := by
  rw [value84, value85, value86, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(317 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (308 : Vertex) [(317 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 212 = true ∨ valuation q 81 = true ∨ valuation q 86 = true := by
  rw [value81, value84, value86, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(308 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (317 : Vertex) [(308 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 212 = true ∨ valuation q 81 = true ∨ valuation q 85 = true := by
  rw [value81, value84, value85, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(308 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (318 : Vertex) [(308 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 213 = true ∨ valuation q 76 = true := by
  rw [value76, value85, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (316 : Vertex) → w ∈ [(301 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (316 : Vertex) [(301 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 17 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value17, value82, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (62 : Vertex) (310 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value82, value83, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (310 : Vertex) (314 : Vertex) (316 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 20 = true := by
  rw [value20, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ∈ [(99 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (355 : Vertex) [(99 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 87 = true := by
  rw [value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 31 = false ∨ valuation q 69 = false ∨ valuation q 89 = false := by
  rw [value31, value69, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (288 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 31 = false ∨ valuation q 69 = false ∨ valuation q 95 = false := by
  rw [value31, value69, value88, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (288 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 31 = false ∨ valuation q 89 = false ∨ valuation q 95 = false := by
  rw [value31, value88, value89, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (417 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 31 = false ∨ valuation q 89 = false ∨ valuation q 111 = false := by
  rw [value31, value88, value89, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (417 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 69 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value69, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (417 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 69 = false ∨ valuation q 89 = false ∨ valuation q 91 = false := by
  rw [value69, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (417 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 69 = false ∨ valuation q 89 = false ∨ valuation q 111 = false := by
  rw [value69, value88, value89, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (417 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 69 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value69, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (418 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 69 = false ∨ valuation q 90 = false ∨ valuation q 111 = false := by
  rw [value69, value88, value90, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (418 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 69 = false ∨ valuation q 91 = false ∨ valuation q 111 = false := by
  rw [value69, value88, value91, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (420 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E036.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112036
