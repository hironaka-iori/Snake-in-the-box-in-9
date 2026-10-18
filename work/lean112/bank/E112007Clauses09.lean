import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 12 = false ∨ valuation q 65 = false ∨ valuation q 77 = false := by
  rw [value12, value65, value73, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (82 : Vertex) (322 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 55 = false ∨ valuation q 65 = false ∨ valuation q 77 = false := by
  rw [value55, value65, value73, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (274 : Vertex) (322 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 191 = true ∨ valuation q 55 = true ∨ valuation q 65 = true ∨ valuation q 77 = true := by
  rw [value55, value65, value73, value77, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(274 : Vertex), (322 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (82 : Vertex) [(274 : Vertex), (322 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 191 = true ∨ valuation q 12 = true ∨ valuation q 55 = true ∨ valuation q 65 = true := by
  rw [value12, value55, value65, value73, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(82 : Vertex), (274 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (346 : Vertex) [(82 : Vertex), (274 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 192 = true ∨ valuation q 79 = true := by
  rw [value74, value79, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(349 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (343 : Vertex) [(349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 192 = true ∨ valuation q 75 = true := by
  rw [value74, value75, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(343 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (349 : Vertex) [(343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 193 = true ∨ valuation q 74 = true := by
  rw [value74, value75, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(341 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (327 : Vertex) [(341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 193 = true ∨ valuation q 67 = true := by
  rw [value67, value75, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(327 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (341 : Vertex) [(327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 69 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value69, value76, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (329 : Vertex) (347 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 194 = true ∨ valuation q 78 = true ∨ valuation q 79 = true := by
  rw [value76, value78, value79, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(347 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (329 : Vertex) [(347 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 194 = true ∨ valuation q 69 = true ∨ valuation q 79 = true := by
  rw [value69, value76, value79, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(329 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (347 : Vertex) [(329 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 194 = true ∨ valuation q 69 = true ∨ valuation q 78 = true := by
  rw [value69, value76, value78, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(329 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (349 : Vertex) [(329 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 78 = false := by
  rw [value70, value73, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (330 : Vertex) (338 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 195 = true ∨ valuation q 73 = true ∨ valuation q 78 = true := by
  rw [value73, value77, value78, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(338 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (330 : Vertex) [(338 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 195 = true ∨ valuation q 70 = true ∨ valuation q 78 = true := by
  rw [value70, value77, value78, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(330 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (338 : Vertex) [(330 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 195 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value70, value73, value77, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(330 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (347 : Vertex) [(330 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 196 = true ∨ valuation q 77 = true := by
  rw [value77, value78, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(346 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (345 : Vertex) [(346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 196 = true ∨ valuation q 76 = true := by
  rw [value76, value78, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(345 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (346 : Vertex) [(345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 197 = true ∨ valuation q 76 = true := by
  rw [value76, value79, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(345 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (341 : Vertex) [(345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 197 = true ∨ valuation q 74 = true := by
  rw [value74, value79, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(341 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (345 : Vertex) [(341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 14 = false ∨ valuation q 81 = false ∨ valuation q 83 = false := by
  rw [value14, value80, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (128 : Vertex) (386 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 14 = false ∨ valuation q 81 = false ∨ valuation q 86 = false := by
  rw [value14, value80, value81, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (128 : Vertex) (386 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value80, value81, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 16 = false ∨ valuation q 50 = false ∨ valuation q 84 = false := by
  rw [value16, value50, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (258 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 16 = false ∨ valuation q 50 = false ∨ valuation q 88 = false := by
  rw [value16, value50, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (258 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 16 = false ∨ valuation q 50 = false ∨ valuation q 101 = false := by
  rw [value16, value50, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (258 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 16 = false ∨ valuation q 82 = false ∨ valuation q 101 = false := by
  rw [value16, value81, value82, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (387 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 50 = false ∨ valuation q 80 = false ∨ valuation q 88 = false := by
  rw [value50, value80, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (384 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 50 = false ∨ valuation q 80 = false ∨ valuation q 101 = false := by
  rw [value50, value80, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (384 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 50 = false ∨ valuation q 82 = false ∨ valuation q 101 = false := by
  rw [value50, value81, value82, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (387 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 50 = false ∨ valuation q 84 = false ∨ valuation q 88 = false := by
  rw [value50, value81, value84, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 50 = false ∨ valuation q 84 = false ∨ valuation q 101 = false := by
  rw [value50, value81, value84, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (390 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E007.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112007
