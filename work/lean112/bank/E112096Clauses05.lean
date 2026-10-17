import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 62 = false ∨ valuation q 70 = false ∨ valuation q 113 = false := by
  rw [value62, value70, value71, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (327 : Vertex) (342 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 113 = false := by
  rw [value69, value70, value71, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (341 : Vertex) (342 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 191 = true ∨ valuation q 64 = true ∨ valuation q 75 = true := by
  rw [value64, value73, value75, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(330 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (347 : Vertex) [(330 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 117 = false := by
  rw [value70, value73, value75, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (342 : Vertex) (346 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 81 = false := by
  rw [value76, value77, value78, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 96 = false := by
  rw [value76, value77, value78, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 81 = false ∨ valuation q 96 = false := by
  rw [value76, value77, value81, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (392 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 81 = false ∨ valuation q 96 = false := by
  rw [value76, value78, value81, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (388 : Vertex) (392 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 195 = true ∨ valuation q 79 = true ∨ valuation q 83 = true ∨ valuation q 98 = true := by
  rw [value77, value79, value83, value98, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(390 : Vertex), (394 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (384 : Vertex) [(390 : Vertex), (394 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 195 = true ∨ valuation q 76 = true ∨ valuation q 83 = true ∨ valuation q 98 = true := by
  rw [value76, value77, value83, value98, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(384 : Vertex), (394 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (390 : Vertex) [(384 : Vertex), (394 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 195 = true ∨ valuation q 76 = true ∨ valuation q 79 = true ∨ valuation q 98 = true := by
  rw [value76, value77, value79, value98, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(384 : Vertex), (390 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (394 : Vertex) [(384 : Vertex), (390 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 195 = true ∨ valuation q 76 = true ∨ valuation q 79 = true ∨ valuation q 83 = true := by
  rw [value76, value77, value79, value83, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(384 : Vertex), (390 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (450 : Vertex) [(384 : Vertex), (390 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 76 = false ∨ valuation q 84 = false ∨ valuation q 89 = false := by
  rw [value76, value78, value84, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (396 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 84 = false ∨ valuation q 89 = false := by
  rw [value78, value79, value84, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (390 : Vertex) (396 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 196 = true ∨ valuation q 79 = true ∨ valuation q 84 = true ∨ valuation q 89 = true ∨ valuation q 100 = true := by
  rw [value78, value79, value84, value89, value100, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(390 : Vertex), (396 : Vertex), (404 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (384 : Vertex) [(390 : Vertex), (396 : Vertex), (404 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 196 = true ∨ valuation q 76 = true ∨ valuation q 79 = true ∨ valuation q 84 = true ∨ valuation q 100 = true := by
  rw [value76, value78, value79, value84, value100, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(384 : Vertex), (390 : Vertex), (396 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (404 : Vertex) [(384 : Vertex), (390 : Vertex), (396 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 19 = false ∨ valuation q 51 = false ∨ valuation q 77 = false := by
  rw [value19, value51, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (134 : Vertex) (262 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 19 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value19, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (134 : Vertex) (386 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 19 = false ∨ valuation q 77 = false ∨ valuation q 80 = false := by
  rw [value19, value77, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (134 : Vertex) (386 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 19 = false ∨ valuation q 77 = false ∨ valuation q 86 = false := by
  rw [value19, value77, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (134 : Vertex) (386 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 19 = false ∨ valuation q 78 = false ∨ valuation q 80 = false := by
  rw [value19, value78, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (134 : Vertex) (388 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 19 = false ∨ valuation q 78 = false ∨ valuation q 86 = false := by
  rw [value19, value78, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (134 : Vertex) (388 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 19 = false ∨ valuation q 80 = false ∨ valuation q 86 = false := by
  rw [value19, value79, value80, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (134 : Vertex) (391 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 51 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value51, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (262 : Vertex) (386 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 51 = false ∨ valuation q 77 = false ∨ valuation q 80 = false := by
  rw [value51, value77, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (262 : Vertex) (386 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 51 = false ∨ valuation q 77 = false ∨ valuation q 86 = false := by
  rw [value51, value77, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (262 : Vertex) (386 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 51 = false ∨ valuation q 78 = false ∨ valuation q 80 = false := by
  rw [value51, value78, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (262 : Vertex) (388 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 51 = false ∨ valuation q 78 = false ∨ valuation q 86 = false := by
  rw [value51, value78, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (262 : Vertex) (388 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 51 = false ∨ valuation q 80 = false ∨ valuation q 86 = false := by
  rw [value51, value79, value80, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (262 : Vertex) (391 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 80 = false := by
  rw [value77, value78, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 86 = false := by
  rw [value77, value78, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 77 = false ∨ valuation q 80 = false ∨ valuation q 86 = false := by
  rw [value77, value79, value80, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (391 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E096.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112096
