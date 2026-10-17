import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 54 = false ∨ valuation q 71 = false ∨ valuation q 109 = false := by
  rw [value54, value60, value71, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (223 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 71 = false := by
  rw [value58, value59, value60, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (205 : Vertex) (206 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 109 = false := by
  rw [value58, value59, value60, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (205 : Vertex) (206 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 58 = false ∨ valuation q 71 = false ∨ valuation q 109 = false := by
  rw [value58, value60, value71, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (205 : Vertex) (223 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 59 = false ∨ valuation q 71 = false ∨ valuation q 109 = false := by
  rw [value59, value60, value71, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (206 : Vertex) (223 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 179 = true ∨ valuation q 49 = true ∨ valuation q 62 = true ∨ valuation q 64 = true := by
  rw [value49, value61, value62, value64, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(192 : Vertex), (209 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (144 : Vertex) [(192 : Vertex), (209 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 179 = true ∨ valuation q 40 = true ∨ valuation q 62 = true ∨ valuation q 64 = true := by
  rw [value40, value61, value62, value64, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(144 : Vertex), (209 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (192 : Vertex) [(144 : Vertex), (209 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 179 = true ∨ valuation q 40 = true ∨ valuation q 49 = true ∨ valuation q 64 = true := by
  rw [value40, value49, value61, value64, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(144 : Vertex), (192 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (209 : Vertex) [(144 : Vertex), (192 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 179 = true ∨ valuation q 40 = true ∨ valuation q 49 = true ∨ valuation q 62 = true := by
  rw [value40, value49, value61, value62, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(144 : Vertex), (192 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (212 : Vertex) [(144 : Vertex), (192 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 50 = false ∨ valuation q 61 = false ∨ valuation q 63 = false := by
  rw [value50, value61, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (193 : Vertex) (208 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 50 = false ∨ valuation q 61 = false ∨ valuation q 65 = false := by
  rw [value50, value61, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (193 : Vertex) (208 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 50 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value50, value62, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (193 : Vertex) (211 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value61, value62, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (208 : Vertex) (211 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 180 = true ∨ valuation q 50 = true ∨ valuation q 61 = true ∨ valuation q 65 = true := by
  rw [value50, value61, value62, value65, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(193 : Vertex), (208 : Vertex), (213 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (211 : Vertex) [(193 : Vertex), (208 : Vertex), (213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 52 = false ∨ valuation q 62 = false ∨ valuation q 67 = false := by
  rw [value52, value62, value63, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (195 : Vertex) (209 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 62 = true ∨ valuation q 66 = true ∨ valuation q 67 = true := by
  rw [value62, value63, value66, value67, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(209 : Vertex), (215 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (195 : Vertex) [(209 : Vertex), (215 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 52 = true ∨ valuation q 66 = true ∨ valuation q 67 = true := by
  rw [value52, value63, value66, value67, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(195 : Vertex), (215 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (209 : Vertex) [(195 : Vertex), (215 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 52 = true ∨ valuation q 62 = true ∨ valuation q 67 = true := by
  rw [value52, value62, value63, value67, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(195 : Vertex), (209 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (215 : Vertex) [(195 : Vertex), (209 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 52 = true ∨ valuation q 62 = true ∨ valuation q 66 = true := by
  rw [value52, value62, value63, value66, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(195 : Vertex), (209 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (219 : Vertex) [(195 : Vertex), (209 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 21 = false ∨ valuation q 42 = false ∨ valuation q 53 = false := by
  rw [value21, value42, value53, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (148 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 21 = false ∨ valuation q 42 = false ∨ valuation q 61 = false := by
  rw [value21, value42, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (148 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 21 = false ∨ valuation q 42 = false ∨ valuation q 68 = false := by
  rw [value21, value42, value64, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (148 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 21 = false ∨ valuation q 53 = false ∨ valuation q 61 = false := by
  rw [value21, value53, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (196 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 21 = false ∨ valuation q 53 = false ∨ valuation q 65 = false := by
  rw [value21, value53, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (196 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 21 = false ∨ valuation q 53 = false ∨ valuation q 68 = false := by
  rw [value21, value53, value64, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (196 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 21 = false ∨ valuation q 53 = false ∨ valuation q 111 = false := by
  rw [value21, value53, value64, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (196 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 21 = false ∨ valuation q 61 = false ∨ valuation q 65 = false := by
  rw [value21, value61, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (208 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 21 = false ∨ valuation q 61 = false ∨ valuation q 68 = false := by
  rw [value21, value61, value64, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (208 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 21 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value21, value64, value65, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (213 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 42 = false ∨ valuation q 53 = false ∨ valuation q 61 = false := by
  rw [value42, value53, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (148 : Vertex) (196 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 42 = false ∨ valuation q 53 = false ∨ valuation q 65 = false := by
  rw [value42, value53, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (148 : Vertex) (196 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 42 = false ∨ valuation q 53 = false ∨ valuation q 68 = false := by
  rw [value42, value53, value64, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (148 : Vertex) (196 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E158.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112158
