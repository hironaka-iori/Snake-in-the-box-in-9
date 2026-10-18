import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 188 = true ∨ valuation q 76 = true := by
  rw [value76, value77, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (351 : Vertex) → w ∈ [(348 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (351 : Vertex) [(348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 73 = false ∨ valuation q 75 = false ∨ valuation q 77 = false := by
  rw [value73, value75, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (343 : Vertex) (347 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 189 = true ∨ valuation q 75 = true ∨ valuation q 77 = true := by
  rw [value75, value77, value78, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(347 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (343 : Vertex) [(347 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 189 = true ∨ valuation q 73 = true ∨ valuation q 75 = true := by
  rw [value73, value75, value78, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(343 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (350 : Vertex) [(343 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 88 = false := by
  rw [value79, value80, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 190 = true ∨ valuation q 81 = true ∨ valuation q 88 = true := by
  rw [value79, value81, value88, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(388 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (386 : Vertex) [(388 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 190 = true ∨ valuation q 80 = true ∨ valuation q 88 = true := by
  rw [value79, value80, value88, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (388 : Vertex) → w ∈ [(386 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (388 : Vertex) [(386 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 190 = true ∨ valuation q 80 = true ∨ valuation q 81 = true := by
  rw [value79, value80, value81, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(386 : Vertex), (388 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (400 : Vertex) [(386 : Vertex), (388 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 44 = false ∨ valuation q 79 = false ∨ valuation q 84 = false := by
  rw [value44, value79, value80, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (384 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 191 = true ∨ valuation q 79 = true ∨ valuation q 83 = true ∨ valuation q 84 = true := by
  rw [value79, value80, value83, value84, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(384 : Vertex), (390 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (258 : Vertex) [(384 : Vertex), (390 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 191 = true ∨ valuation q 44 = true ∨ valuation q 83 = true ∨ valuation q 84 = true := by
  rw [value44, value80, value83, value84, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(258 : Vertex), (390 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (384 : Vertex) [(258 : Vertex), (390 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 191 = true ∨ valuation q 44 = true ∨ valuation q 79 = true ∨ valuation q 84 = true := by
  rw [value44, value79, value80, value84, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(258 : Vertex), (384 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (390 : Vertex) [(258 : Vertex), (384 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 191 = true ∨ valuation q 44 = true ∨ valuation q 79 = true ∨ valuation q 83 = true := by
  rw [value44, value79, value80, value83, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(258 : Vertex), (384 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (394 : Vertex) [(258 : Vertex), (384 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 13 = false ∨ valuation q 79 = false ∨ valuation q 82 = false := by
  rw [value13, value79, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (384 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 13 = false ∨ valuation q 79 = false ∨ valuation q 86 = false := by
  rw [value13, value79, value81, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (384 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 13 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value13, value81, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (390 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 14 = false ∨ valuation q 46 = false ∨ valuation q 87 = false := by
  rw [value14, value46, value82, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 14 = false ∨ valuation q 81 = false ∨ valuation q 87 = false := by
  rw [value14, value81, value82, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (388 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 46 = false ∨ valuation q 81 = false ∨ valuation q 87 = false := by
  rw [value46, value81, value82, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (388 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 193 = true ∨ valuation q 14 = true ∨ valuation q 46 = true ∨ valuation q 81 = true := by
  rw [value14, value46, value81, value82, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(133 : Vertex), (261 : Vertex), (388 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (397 : Vertex) [(133 : Vertex), (261 : Vertex), (388 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 47 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value47, value80, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (262 : Vertex) (386 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 194 = true ∨ valuation q 47 = true ∨ valuation q 81 = true := by
  rw [value47, value81, value83, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(262 : Vertex), (388 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (386 : Vertex) [(262 : Vertex), (388 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 17 = false ∨ valuation q 51 = false ∨ valuation q 80 = false := by
  rw [value17, value51, value80, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (266 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 17 = false ∨ valuation q 51 = false ∨ valuation q 85 = false := by
  rw [value17, value51, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (266 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 17 = false ∨ valuation q 80 = false ∨ valuation q 85 = false := by
  rw [value17, value80, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (386 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 51 = false ∨ valuation q 80 = false ∨ valuation q 85 = false := by
  rw [value51, value80, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (386 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 18 = false ∨ valuation q 52 = false ∨ valuation q 84 = false := by
  rw [value18, value52, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (267 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 18 = false ∨ valuation q 52 = false ∨ valuation q 92 = false := by
  rw [value18, value52, value85, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (267 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 52 = false ∨ valuation q 84 = false ∨ valuation q 92 = false := by
  rw [value52, value84, value85, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (267 : Vertex) (394 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 196 = true ∨ valuation q 52 = true ∨ valuation q 84 = true ∨ valuation q 92 = true := by
  rw [value52, value84, value85, value92, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(267 : Vertex), (394 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (139 : Vertex) [(267 : Vertex), (394 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 196 = true ∨ valuation q 18 = true ∨ valuation q 84 = true ∨ valuation q 92 = true := by
  rw [value18, value84, value85, value92, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(139 : Vertex), (394 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (267 : Vertex) [(139 : Vertex), (394 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 196 = true ∨ valuation q 18 = true ∨ valuation q 52 = true ∨ valuation q 92 = true := by
  rw [value18, value52, value85, value92, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(139 : Vertex), (267 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (394 : Vertex) [(139 : Vertex), (267 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E161.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112161
