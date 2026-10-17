import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 187 = true ∨ valuation q 30 = true ∨ valuation q 50 = true := by
  rw [value30, value50, value67, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (240 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(112 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (240 : Vertex) (248 : Vertex) [(112 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 189 = true ∨ valuation q 70 = true := by
  rw [value69, value70, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(247 : Vertex)] := by decide
  have hg := other_cover q (245 : Vertex) (229 : Vertex) [(247 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 189 = true ∨ valuation q 61 = true := by
  rw [value61, value69, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(229 : Vertex)] := by decide
  have hg := other_cover q (245 : Vertex) (247 : Vertex) [(229 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 35 = false ∨ valuation q 69 = false ∨ valuation q 74 = false := by
  rw [value35, value69, value70, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (247 : Vertex) (119 : Vertex) (245 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 74 = false := by
  rw [value68, value69, value70, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (247 : Vertex) (243 : Vertex) (245 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 190 = true ∨ valuation q 35 = true ∨ valuation q 69 = true ∨ valuation q 74 = true := by
  rw [value35, value69, value70, value74, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(119 : Vertex), (245 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (243 : Vertex) [(119 : Vertex), (245 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 190 = true ∨ valuation q 35 = true ∨ valuation q 68 = true ∨ valuation q 74 = true := by
  rw [value35, value68, value70, value74, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(119 : Vertex), (243 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (245 : Vertex) [(119 : Vertex), (243 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 36 = false ∨ valuation q 55 = false ∨ valuation q 72 = false := by
  rw [value36, value55, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (120 : Vertex) (184 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 191 = true ∨ valuation q 55 = true ∨ valuation q 67 = true ∨ valuation q 72 = true := by
  rw [value55, value67, value71, value72, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(184 : Vertex), (240 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (120 : Vertex) [(184 : Vertex), (240 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 191 = true ∨ valuation q 36 = true ∨ valuation q 67 = true ∨ valuation q 72 = true := by
  rw [value36, value67, value71, value72, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(120 : Vertex), (240 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (184 : Vertex) [(120 : Vertex), (240 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 191 = true ∨ valuation q 36 = true ∨ valuation q 55 = true ∨ valuation q 72 = true := by
  rw [value36, value55, value71, value72, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(120 : Vertex), (184 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (240 : Vertex) [(120 : Vertex), (184 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 191 = true ∨ valuation q 36 = true ∨ valuation q 55 = true ∨ valuation q 67 = true := by
  rw [value36, value55, value67, value71, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(120 : Vertex), (184 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (249 : Vertex) [(120 : Vertex), (184 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 37 = false ∨ valuation q 63 = false ∨ valuation q 71 = false := by
  rw [value37, value63, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (121 : Vertex) (233 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 192 = true ∨ valuation q 37 = true ∨ valuation q 71 = true := by
  rw [value37, value71, value72, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(121 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (233 : Vertex) [(121 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 192 = true ∨ valuation q 37 = true ∨ valuation q 63 = true := by
  rw [value37, value63, value72, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(121 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (248 : Vertex) [(121 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 41 = false ∨ valuation q 66 = false ∨ valuation q 74 = false := by
  rw [value41, value66, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (254 : Vertex) (126 : Vertex) (238 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 193 = true ∨ valuation q 66 = true ∨ valuation q 74 = true := by
  rw [value66, value73, value74, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(238 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (126 : Vertex) [(238 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 193 = true ∨ valuation q 41 = true ∨ valuation q 74 = true := by
  rw [value41, value73, value74, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(126 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (238 : Vertex) [(126 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 193 = true ∨ valuation q 41 = true ∨ valuation q 66 = true := by
  rw [value41, value66, value73, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(126 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (255 : Vertex) [(126 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 42 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value42, value70, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (127 : Vertex) (247 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 42 = false ∨ valuation q 70 = false ∨ valuation q 120 = false := by
  rw [value42, value70, value74, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (127 : Vertex) (247 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 42 = false ∨ valuation q 73 = false ∨ valuation q 120 = false := by
  rw [value42, value73, value74, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (127 : Vertex) (254 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 120 = false := by
  rw [value70, value73, value74, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (247 : Vertex) (254 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 80 = false := by
  rw [value75, value76, value77, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (290 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 92 = false := by
  rw [value75, value76, value77, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (290 : Vertex) (352 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 80 = false ∨ valuation q 92 = false := by
  rw [value75, value76, value80, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (352 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 80 = false ∨ valuation q 92 = false := by
  rw [value75, value77, value80, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (290 : Vertex) (296 : Vertex) (352 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 195 = true ∨ valuation q 77 = true ∨ valuation q 80 = true ∨ valuation q 92 = true := by
  rw [value75, value77, value80, value92, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(290 : Vertex), (296 : Vertex), (352 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (289 : Vertex) [(290 : Vertex), (296 : Vertex), (352 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 196 = true ∨ valuation q 78 = true := by
  rw [value76, value78, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(291 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (288 : Vertex) [(291 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 196 = true ∨ valuation q 75 = true := by
  rw [value75, value76, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (291 : Vertex) → w ∈ [(288 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (291 : Vertex) [(288 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 197 = true ∨ valuation q 75 = true ∨ valuation q 78 = true ∨ valuation q 84 = true := by
  rw [value75, value77, value78, value84, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (290 : Vertex) w → w ∈ region → w ≠ (34 : Vertex) → w ∈ [(288 : Vertex), (291 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (290 : Vertex) (34 : Vertex) [(288 : Vertex), (291 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value76, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (291 : Vertex) (289 : Vertex) (290 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E040.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112040
