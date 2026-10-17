import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 77 = false ∨ valuation q 115 = false := by
  rw [value33, value75, value77, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (59 : Vertex) (191 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 53 = false ∨ valuation q 69 = false ∨ valuation q 73 = false := by
  rw [value53, value69, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (155 : Vertex) (179 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 53 = false ∨ valuation q 69 = false ∨ valuation q 115 = false := by
  rw [value53, value69, value75, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (155 : Vertex) (179 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 53 = false ∨ valuation q 73 = false ∨ valuation q 77 = false := by
  rw [value53, value73, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (155 : Vertex) (185 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 53 = false ∨ valuation q 77 = false ∨ valuation q 115 = false := by
  rw [value53, value75, value77, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (155 : Vertex) (191 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 69 = false ∨ valuation q 73 = false ∨ valuation q 77 = false := by
  rw [value69, value73, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (179 : Vertex) (185 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 34 = false ∨ valuation q 54 = false ∨ valuation q 64 = false := by
  rw [value34, value54, value64, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (60 : Vertex) (156 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 34 = false ∨ valuation q 54 = false ∨ valuation q 70 = false := by
  rw [value34, value54, value70, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (60 : Vertex) (156 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 34 = false ∨ valuation q 54 = false ∨ valuation q 72 = false := by
  rw [value34, value54, value72, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (60 : Vertex) (156 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 34 = false ∨ valuation q 64 = false ∨ valuation q 70 = false := by
  rw [value34, value64, value70, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (60 : Vertex) (172 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 34 = false ∨ valuation q 64 = false ∨ valuation q 72 = false := by
  rw [value34, value64, value72, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (60 : Vertex) (172 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 54 = false ∨ valuation q 64 = false ∨ valuation q 70 = false := by
  rw [value54, value64, value70, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (156 : Vertex) (172 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 54 = false ∨ valuation q 64 = false ∨ valuation q 72 = false := by
  rw [value54, value64, value72, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (156 : Vertex) (172 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 192 = true ∨ valuation q 54 = true ∨ valuation q 64 = true ∨ valuation q 70 = true ∨ valuation q 72 = true := by
  rw [value54, value64, value70, value72, value76, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (60 : Vertex) → w ∈ [(156 : Vertex), (172 : Vertex), (180 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (60 : Vertex) [(156 : Vertex), (172 : Vertex), (180 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 66 = false ∨ valuation q 71 = false ∨ valuation q 75 = false := by
  rw [value66, value71, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (183 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 194 = true := by
  rw [value78, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (248 : Vertex) (184 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 195 = true ∨ valuation q 97 = true := by
  rw [value79, value97, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(385 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (261 : Vertex) [(385 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 195 = true ∨ valuation q 80 = true := by
  rw [value79, value80, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(261 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (385 : Vertex) [(261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 196 = true ∨ valuation q 87 = true := by
  rw [value80, value87, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(293 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (257 : Vertex) [(293 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 196 = true ∨ valuation q 79 = true := by
  rw [value79, value80, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (293 : Vertex) → w ∈ [(257 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (293 : Vertex) [(257 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 197 = true ∨ valuation q 98 = true := by
  rw [value81, value98, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(392 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (268 : Vertex) [(392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 197 = true ∨ valuation q 83 = true := by
  rw [value81, value83, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(268 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (392 : Vertex) [(268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 198 = true ∨ valuation q 90 = true := by
  rw [value82, value90, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(299 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (271 : Vertex) [(299 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 198 = true ∨ valuation q 84 = true := by
  rw [value82, value84, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(271 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (299 : Vertex) [(271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 199 = true ∨ valuation q 91 = true := by
  rw [value83, value91, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(300 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (264 : Vertex) [(300 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 199 = true ∨ valuation q 81 = true := by
  rw [value81, value83, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (300 : Vertex) → w ∈ [(264 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (300 : Vertex) [(264 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 200 = true ∨ valuation q 101 = true := by
  rw [value84, value101, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(399 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (267 : Vertex) [(399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 200 = true ∨ valuation q 82 = true := by
  rw [value82, value84, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(267 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (399 : Vertex) [(267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 201 = true ∨ valuation q 94 = true := by
  rw [value85, value94, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(307 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (279 : Vertex) [(307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 201 = true ∨ valuation q 86 = true := by
  rw [value85, value86, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(279 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (307 : Vertex) [(279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 202 = true ∨ valuation q 102 = true := by
  rw [value86, value102, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (275 : Vertex) [(407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 202 = true ∨ valuation q 85 = true := by
  rw [value85, value86, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(275 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (407 : Vertex) [(275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block14 (q : Snake 81) (h : Conditions q) : B112E257.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112257
