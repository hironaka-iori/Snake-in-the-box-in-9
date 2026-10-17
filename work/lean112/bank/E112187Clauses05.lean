import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 190 = true ∨ valuation q 66 = true ∨ valuation q 69 = true := by
  rw [value66, value69, value71, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (364 : Vertex) → w ∈ [(358 : Vertex), (362 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (364 : Vertex) [(358 : Vertex), (362 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 191 = true ∨ valuation q 64 = true ∨ valuation q 73 = true := by
  rw [value64, value72, value73, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(356 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (308 : Vertex) [(356 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 191 = true ∨ valuation q 57 = true ∨ valuation q 64 = true := by
  rw [value57, value64, value72, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(308 : Vertex), (356 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (373 : Vertex) [(308 : Vertex), (356 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 65 = false ∨ valuation q 72 = false ∨ valuation q 74 = false := by
  rw [value65, value72, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (357 : Vertex) (372 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 193 = true ∨ valuation q 73 = true ∨ valuation q 79 = true := by
  rw [value73, value74, value79, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(373 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (359 : Vertex) [(373 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 193 = true ∨ valuation q 67 = true ∨ valuation q 79 = true := by
  rw [value67, value74, value79, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(359 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (373 : Vertex) [(359 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 116 = false := by
  rw [value75, value76, value77, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (377 : Vertex) (378 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 194 = true ∨ valuation q 76 = true ∨ valuation q 77 = true := by
  rw [value75, value76, value77, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(377 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (504 : Vertex) [(377 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 68 = false ∨ valuation q 75 = false ∨ valuation q 78 = false := by
  rw [value68, value75, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (377 : Vertex) (361 : Vertex) (376 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 195 = true ∨ valuation q 75 = true ∨ valuation q 78 = true := by
  rw [value75, value76, value78, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (377 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(376 : Vertex), (379 : Vertex)] := by decide
  have hg := other_cover q (377 : Vertex) (361 : Vertex) [(376 : Vertex), (379 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 24 = false ∨ valuation q 59 = false ∨ valuation q 69 = false := by
  rw [value24, value59, value69, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (314 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 24 = false ∨ valuation q 59 = false ∨ valuation q 75 = false := by
  rw [value24, value59, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (314 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 24 = false ∨ valuation q 59 = false ∨ valuation q 78 = false := by
  rw [value24, value59, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (314 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 24 = false ∨ valuation q 69 = false ∨ valuation q 78 = false := by
  rw [value24, value69, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 24 = false ∨ valuation q 75 = false ∨ valuation q 78 = false := by
  rw [value24, value75, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (376 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 59 = false ∨ valuation q 69 = false ∨ valuation q 75 = false := by
  rw [value59, value69, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (362 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 59 = false ∨ valuation q 69 = false ∨ valuation q 78 = false := by
  rw [value59, value69, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 59 = false ∨ valuation q 75 = false ∨ valuation q 78 = false := by
  rw [value59, value75, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (376 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value76, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (377 : Vertex) (378 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 197 = true ∨ valuation q 77 = true ∨ valuation q 79 = true := by
  rw [value77, value78, value79, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(378 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (377 : Vertex) [(378 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 197 = true ∨ valuation q 76 = true ∨ valuation q 79 = true := by
  rw [value76, value78, value79, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(377 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (378 : Vertex) [(377 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 197 = true ∨ valuation q 76 = true ∨ valuation q 77 = true := by
  rw [value76, value77, value78, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(377 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (383 : Vertex) [(377 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 198 = true ∨ valuation q 78 = true := by
  rw [value78, value79, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ≠ (375 : Vertex) → w ∈ [(379 : Vertex)] := by decide
  have hg := other_cover q (383 : Vertex) (375 : Vertex) [(379 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 198 = true ∨ valuation q 74 = true := by
  rw [value74, value79, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(375 : Vertex)] := by decide
  have hg := other_cover q (383 : Vertex) (379 : Vertex) [(375 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 28 = false ∨ valuation q 45 = false ∨ valuation q 83 = false := by
  rw [value28, value45, value80, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (288 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 28 = false ∨ valuation q 45 = false ∨ valuation q 103 = false := by
  rw [value28, value45, value80, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (288 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 28 = false ∨ valuation q 81 = false ∨ valuation q 83 = false := by
  rw [value28, value80, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (417 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 29 = false ∨ valuation q 46 = false ∨ valuation q 80 = false := by
  rw [value29, value46, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 29 = false ∨ valuation q 46 = false ∨ valuation q 84 = false := by
  rw [value29, value46, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 29 = false ∨ valuation q 46 = false ∨ valuation q 93 = false := by
  rw [value29, value46, value81, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 29 = false ∨ valuation q 46 = false ∨ valuation q 104 = false := by
  rw [value29, value46, value81, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 29 = false ∨ valuation q 84 = false ∨ valuation q 104 = false := by
  rw [value29, value81, value84, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E187.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112187
