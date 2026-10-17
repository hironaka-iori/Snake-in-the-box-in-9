import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 192 = true ∨ valuation q 19 = true ∨ valuation q 55 = true ∨ valuation q 75 = true ∨ valuation q 78 = true ∨ valuation q 87 = true := by
  rw [value19, value55, value75, value76, value78, value87, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (225 : Vertex) → w ∈ [(33 : Vertex), (129 : Vertex), (160 : Vertex), (163 : Vertex), (177 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (225 : Vertex) [(33 : Vertex), (129 : Vertex), (160 : Vertex), (163 : Vertex), (177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 82 = false := by
  rw [value75, value77, value78, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (163 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 88 = false := by
  rw [value75, value77, value78, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (163 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 75 = false ∨ valuation q 82 = false ∨ valuation q 88 = false := by
  rw [value75, value77, value82, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (170 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 82 = false ∨ valuation q 88 = false := by
  rw [value77, value78, value82, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (163 : Vertex) (170 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 193 = true ∨ valuation q 75 = true ∨ valuation q 78 = true ∨ valuation q 88 = true := by
  rw [value75, value77, value78, value88, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (170 : Vertex) [(160 : Vertex), (163 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 20 = false ∨ valuation q 56 = false ∨ valuation q 80 = false := by
  rw [value20, value56, value78, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (131 : Vertex) (167 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 20 = false ∨ valuation q 56 = false ∨ valuation q 83 = false := by
  rw [value20, value56, value78, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (131 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 20 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value20, value76, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (161 : Vertex) (162 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 20 = false ∨ valuation q 76 = false ∨ valuation q 80 = false := by
  rw [value20, value76, value78, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (161 : Vertex) (167 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 20 = false ∨ valuation q 76 = false ∨ valuation q 83 = false := by
  rw [value20, value76, value78, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (161 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 20 = false ∨ valuation q 77 = false ∨ valuation q 80 = false := by
  rw [value20, value77, value78, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (162 : Vertex) (167 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 20 = false ∨ valuation q 77 = false ∨ valuation q 83 = false := by
  rw [value20, value77, value78, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (162 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 20 = false ∨ valuation q 80 = false ∨ valuation q 105 = false := by
  rw [value20, value78, value80, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (167 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 20 = false ∨ valuation q 83 = false ∨ valuation q 105 = false := by
  rw [value20, value78, value83, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (171 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 56 = false ∨ valuation q 76 = false ∨ valuation q 80 = false := by
  rw [value56, value76, value78, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (131 : Vertex) (161 : Vertex) (167 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 56 = false ∨ valuation q 76 = false ∨ valuation q 83 = false := by
  rw [value56, value76, value78, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (131 : Vertex) (161 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 56 = false ∨ valuation q 80 = false ∨ valuation q 83 = false := by
  rw [value56, value78, value80, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (131 : Vertex) (167 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 21 = false ∨ valuation q 57 = false ∨ valuation q 75 = false := by
  rw [value21, value57, value75, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (164 : Vertex) (36 : Vertex) (132 : Vertex) (160 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 21 = false ∨ valuation q 57 = false ∨ valuation q 84 = false := by
  rw [value21, value57, value79, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (164 : Vertex) (36 : Vertex) (132 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 21 = false ∨ valuation q 57 = false ∨ valuation q 89 = false := by
  rw [value21, value57, value79, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (164 : Vertex) (36 : Vertex) (132 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 21 = false ∨ valuation q 75 = false ∨ valuation q 84 = false := by
  rw [value21, value75, value79, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (164 : Vertex) (36 : Vertex) (160 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 21 = false ∨ valuation q 75 = false ∨ valuation q 89 = false := by
  rw [value21, value75, value79, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (164 : Vertex) (36 : Vertex) (160 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 21 = false ∨ valuation q 84 = false ∨ valuation q 89 = false := by
  rw [value21, value79, value84, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (164 : Vertex) (36 : Vertex) (172 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 57 = false ∨ valuation q 75 = false ∨ valuation q 89 = false := by
  rw [value57, value75, value79, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (164 : Vertex) (132 : Vertex) (160 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 57 = false ∨ valuation q 84 = false ∨ valuation q 89 = false := by
  rw [value57, value79, value84, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (164 : Vertex) (132 : Vertex) (172 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 21 = false ∨ valuation q 84 = false := by
  rw [value21, value84, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (164 : Vertex) (36 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 195 = true ∨ valuation q 57 = true ∨ valuation q 75 = true ∨ valuation q 84 = true ∨ valuation q 89 = true := by
  rw [value57, value75, value79, value84, value89, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(132 : Vertex), (160 : Vertex), (172 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (36 : Vertex) [(132 : Vertex), (160 : Vertex), (172 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 195 = true ∨ valuation q 21 = true ∨ valuation q 57 = true ∨ valuation q 75 = true ∨ valuation q 89 = true := by
  rw [value21, value57, value75, value79, value89, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(36 : Vertex), (132 : Vertex), (160 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (172 : Vertex) [(36 : Vertex), (132 : Vertex), (160 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 195 = true ∨ valuation q 21 = true ∨ valuation q 57 = true ∨ valuation q 75 = true ∨ valuation q 84 = true := by
  rw [value21, value57, value75, value79, value84, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(36 : Vertex), (132 : Vertex), (160 : Vertex), (172 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (180 : Vertex) [(36 : Vertex), (132 : Vertex), (160 : Vertex), (172 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 78 = false ∨ valuation q 85 = false ∨ valuation q 91 = false := by
  rw [value78, value80, value85, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (167 : Vertex) (163 : Vertex) (175 : Vertex) (183 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 196 = true ∨ valuation q 78 = true ∨ valuation q 85 = true := by
  rw [value78, value80, value85, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(163 : Vertex), (175 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (183 : Vertex) [(163 : Vertex), (175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block13 (q : Snake 81) (h : Conditions q) : B112E259.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112259
