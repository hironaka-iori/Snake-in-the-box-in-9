import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 58 = true ∨ valuation q 59 = true ∨ valuation q 69 = true := by
  rw [value58, value59, value60, value69, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (231 : Vertex) → w ∈ [(235 : Vertex), (237 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (239 : Vertex) (231 : Vertex) [(235 : Vertex), (237 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 55 = true ∨ valuation q 59 = true ∨ valuation q 69 = true := by
  rw [value55, value59, value60, value69, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(231 : Vertex), (237 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (239 : Vertex) (235 : Vertex) [(231 : Vertex), (237 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 55 = true ∨ valuation q 58 = true ∨ valuation q 69 = true := by
  rw [value55, value58, value60, value69, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(231 : Vertex), (235 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (239 : Vertex) (237 : Vertex) [(231 : Vertex), (235 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 55 = true ∨ valuation q 58 = true ∨ valuation q 59 = true := by
  rw [value55, value58, value59, value60, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(231 : Vertex), (235 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (239 : Vertex) (255 : Vertex) [(231 : Vertex), (235 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value61, value62, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (241 : Vertex) (244 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value61, value63, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (242 : Vertex) (244 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 64 = true := by
  rw [value62, value64, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(243 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (240 : Vertex) [(243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 61 = true := by
  rw [value61, value62, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(240 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (243 : Vertex) [(240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 43 = false ∨ valuation q 61 = false ∨ valuation q 117 = false := by
  rw [value43, value61, value63, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (242 : Vertex) (178 : Vertex) (240 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 52 = false ∨ valuation q 64 = false ∨ valuation q 117 = false := by
  rw [value52, value63, value64, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (242 : Vertex) (226 : Vertex) (243 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 188 = true ∨ valuation q 53 = true ∨ valuation q 63 = true := by
  rw [value53, value63, value64, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (241 : Vertex) → w ∈ [(227 : Vertex), (242 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (241 : Vertex) [(227 : Vertex), (242 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 61 = false ∨ valuation q 67 = false ∨ valuation q 118 = false := by
  rw [value61, value65, value67, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (240 : Vertex) (252 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 67 = true ∨ valuation q 118 = true := by
  rw [value65, value67, value118, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(252 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (240 : Vertex) [(252 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 61 = true ∨ valuation q 118 = true := by
  rw [value61, value65, value118, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(240 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (252 : Vertex) [(240 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 47 = false ∨ valuation q 61 = false ∨ valuation q 67 = false := by
  rw [value47, value61, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (184 : Vertex) (240 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 47 = true ∨ valuation q 67 = true := by
  rw [value47, value66, value67, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(184 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (240 : Vertex) [(184 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 47 = true ∨ valuation q 61 = true := by
  rw [value47, value61, value66, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(184 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (252 : Vertex) [(184 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value65, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (252 : Vertex) (244 : Vertex) (248 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 191 = true ∨ valuation q 65 = true ∨ valuation q 66 = true := by
  rw [value65, value66, value67, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (252 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(244 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (252 : Vertex) (254 : Vertex) [(244 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 69 = true := by
  rw [value68, value69, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(255 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (252 : Vertex) [(255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 67 = true := by
  rw [value67, value68, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(252 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (255 : Vertex) [(252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 68 = false := by
  rw [value51, value60, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (191 : Vertex) (239 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 193 = true ∨ valuation q 51 = true ∨ valuation q 60 = true := by
  rw [value51, value60, value69, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(191 : Vertex), (239 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (254 : Vertex) [(191 : Vertex), (239 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 74 = false ∨ valuation q 86 = false := by
  rw [value70, value71, value74, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 71 = false ∨ valuation q 74 = false := by
  rw [value71, value74, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 194 = true ∨ valuation q 74 = true ∨ valuation q 86 = true := by
  rw [value70, value74, value86, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(296 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (289 : Vertex) [(296 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 194 = true ∨ valuation q 71 = true ∨ valuation q 86 = true := by
  rw [value70, value71, value86, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(289 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (296 : Vertex) [(289 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 1 = false ∨ valuation q 70 = false ∨ valuation q 87 = false := by
  rw [value1, value70, value71, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (33 : Vertex) (288 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 1 = false ∨ valuation q 75 = false ∨ valuation q 87 = false := by
  rw [value1, value71, value75, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (33 : Vertex) (297 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 70 = true ∨ valuation q 75 = true ∨ valuation q 87 = true := by
  rw [value70, value71, value75, value87, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(288 : Vertex), (297 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (33 : Vertex) [(288 : Vertex), (297 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 1 = true ∨ valuation q 75 = true ∨ valuation q 87 = true := by
  rw [value1, value71, value75, value87, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(33 : Vertex), (297 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (288 : Vertex) [(33 : Vertex), (297 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 1 = true ∨ valuation q 70 = true ∨ valuation q 87 = true := by
  rw [value1, value70, value71, value87, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(33 : Vertex), (288 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (297 : Vertex) [(33 : Vertex), (288 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block12 (q : Snake 81) (h : Conditions q) : B112E008.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112008
