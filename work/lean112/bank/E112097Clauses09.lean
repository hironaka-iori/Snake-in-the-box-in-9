import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 78 = false ∨ valuation q 107 = false := by
  rw [value70, value71, value78, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (361 : Vertex) (376 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 193 = true ∨ valuation q 71 = true ∨ valuation q 78 = true ∨ valuation q 107 = true := by
  rw [value70, value71, value78, value107, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(361 : Vertex), (376 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (296 : Vertex) [(361 : Vertex), (376 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 193 = true ∨ valuation q 52 = true ∨ valuation q 78 = true ∨ valuation q 107 = true := by
  rw [value52, value70, value78, value107, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(296 : Vertex), (376 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (361 : Vertex) [(296 : Vertex), (376 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 193 = true ∨ valuation q 52 = true ∨ valuation q 71 = true ∨ valuation q 107 = true := by
  rw [value52, value70, value71, value107, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (376 : Vertex) → w ∈ [(296 : Vertex), (361 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (376 : Vertex) [(296 : Vertex), (361 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 193 = true ∨ valuation q 52 = true ∨ valuation q 71 = true ∨ valuation q 78 = true := by
  rw [value52, value70, value71, value78, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(296 : Vertex), (361 : Vertex), (376 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (488 : Vertex) [(296 : Vertex), (361 : Vertex), (376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 53 = false ∨ valuation q 65 = false ∨ valuation q 70 = false := by
  rw [value53, value65, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (361 : Vertex) (297 : Vertex) (353 : Vertex) (360 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 53 = false ∨ valuation q 65 = false ∨ valuation q 108 = false := by
  rw [value53, value65, value71, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (361 : Vertex) (297 : Vertex) (353 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 53 = false ∨ valuation q 70 = false ∨ valuation q 108 = false := by
  rw [value53, value70, value71, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (361 : Vertex) (297 : Vertex) (360 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 65 = false ∨ valuation q 70 = false ∨ valuation q 108 = false := by
  rw [value65, value70, value71, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (361 : Vertex) (353 : Vertex) (360 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 195 = true ∨ valuation q 68 = true ∨ valuation q 73 = true ∨ valuation q 112 = true := by
  rw [value68, value72, value73, value112, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(358 : Vertex), (367 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (302 : Vertex) [(358 : Vertex), (367 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 195 = true ∨ valuation q 56 = true ∨ valuation q 73 = true ∨ valuation q 112 = true := by
  rw [value56, value72, value73, value112, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (358 : Vertex) → w ∈ [(302 : Vertex), (367 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (358 : Vertex) [(302 : Vertex), (367 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 195 = true ∨ valuation q 56 = true ∨ valuation q 68 = true ∨ valuation q 112 = true := by
  rw [value56, value68, value72, value112, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(302 : Vertex), (358 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (367 : Vertex) [(302 : Vertex), (358 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 195 = true ∨ valuation q 56 = true ∨ valuation q 68 = true ∨ valuation q 73 = true := by
  rw [value56, value68, value72, value73, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (494 : Vertex) → w ∈ [(302 : Vertex), (358 : Vertex), (367 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (494 : Vertex) [(302 : Vertex), (358 : Vertex), (367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 81 = false := by
  rw [value69, value72, value73, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (359 : Vertex) (366 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 113 = false := by
  rw [value69, value72, value73, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (359 : Vertex) (366 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 69 = false ∨ valuation q 81 = false ∨ valuation q 113 = false := by
  rw [value69, value73, value81, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (359 : Vertex) (383 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 72 = false ∨ valuation q 81 = false ∨ valuation q 113 = false := by
  rw [value72, value73, value81, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (366 : Vertex) (383 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 196 = true ∨ valuation q 69 = true ∨ valuation q 81 = true ∨ valuation q 113 = true := by
  rw [value69, value73, value81, value113, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(359 : Vertex), (383 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (366 : Vertex) [(359 : Vertex), (383 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 196 = true ∨ valuation q 69 = true ∨ valuation q 72 = true ∨ valuation q 113 = true := by
  rw [value69, value72, value73, value113, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(359 : Vertex), (366 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (383 : Vertex) [(359 : Vertex), (366 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 197 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value74, value77, value78, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ≠ (370 : Vertex) → w ∈ [(372 : Vertex), (376 : Vertex)] := by decide
  have hg := other_cover q (368 : Vertex) (370 : Vertex) [(372 : Vertex), (376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 197 = true ∨ valuation q 75 = true ∨ valuation q 78 = true := by
  rw [value74, value75, value78, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ≠ (372 : Vertex) → w ∈ [(370 : Vertex), (376 : Vertex)] := by decide
  have hg := other_cover q (368 : Vertex) (372 : Vertex) [(370 : Vertex), (376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 197 = true ∨ valuation q 75 = true ∨ valuation q 77 = true := by
  rw [value74, value75, value77, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ≠ (376 : Vertex) → w ∈ [(370 : Vertex), (372 : Vertex)] := by decide
  have hg := other_cover q (368 : Vertex) (376 : Vertex) [(370 : Vertex), (372 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 74 = false ∨ valuation q 76 = false := by
  rw [value74, value76, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (370 : Vertex) (368 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 198 = true ∨ valuation q 76 = true := by
  rw [value75, value76, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (370 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(371 : Vertex)] := by decide
  have hg := other_cover q (370 : Vertex) (368 : Vertex) [(371 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 198 = true ∨ valuation q 74 = true := by
  rw [value74, value75, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (370 : Vertex) w → w ∈ region → w ≠ (371 : Vertex) → w ∈ [(368 : Vertex)] := by decide
  have hg := other_cover q (370 : Vertex) (371 : Vertex) [(368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 199 = true ∨ valuation q 58 = true ∨ valuation q 75 = true := by
  rw [value58, value75, value76, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (371 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(307 : Vertex), (370 : Vertex)] := by decide
  have hg := other_cover q (371 : Vertex) (355 : Vertex) [(307 : Vertex), (370 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 199 = true ∨ valuation q 58 = true ∨ valuation q 66 = true := by
  rw [value58, value66, value76, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (371 : Vertex) w → w ∈ region → w ≠ (370 : Vertex) → w ∈ [(307 : Vertex), (355 : Vertex)] := by decide
  have hg := other_cover q (371 : Vertex) (370 : Vertex) [(307 : Vertex), (355 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 59 = false ∨ valuation q 74 = false ∨ valuation q 79 = false := by
  rw [value59, value74, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (372 : Vertex) (308 : Vertex) (368 : Vertex) (380 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 59 = false ∨ valuation q 74 = false ∨ valuation q 115 = false := by
  rw [value59, value74, value77, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (372 : Vertex) (308 : Vertex) (368 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 74 = false ∨ valuation q 79 = false ∨ valuation q 115 = false := by
  rw [value74, value77, value79, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (372 : Vertex) (368 : Vertex) (380 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 79 = false := by
  rw [value70, value74, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (360 : Vertex) (368 : Vertex) (380 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 74 = false ∨ valuation q 79 = false := by
  rw [value74, value79, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (376 : Vertex) (368 : Vertex) (380 : Vertex) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E097.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112097
