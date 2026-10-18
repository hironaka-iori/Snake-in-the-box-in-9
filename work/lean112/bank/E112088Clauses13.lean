import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 82 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value82, value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (425 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 82 = false ∨ valuation q 87 = false ∨ valuation q 95 = false := by
  rw [value82, value86, value87, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (425 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 82 = false ∨ valuation q 88 = false ∨ valuation q 95 = false := by
  rw [value82, value86, value88, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 95 = false := by
  rw [value86, value87, value88, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (425 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 17 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value17, value83, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (169 : Vertex) (417 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 203 = true ∨ valuation q 83 = true ∨ valuation q 86 = true := by
  rw [value83, value86, value87, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(417 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (169 : Vertex) [(417 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 203 = true ∨ valuation q 17 = true ∨ valuation q 86 = true := by
  rw [value17, value86, value87, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(169 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (417 : Vertex) [(169 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 203 = true ∨ valuation q 17 = true ∨ valuation q 83 = true := by
  rw [value17, value83, value87, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(169 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (424 : Vertex) [(169 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 204 = true ∨ valuation q 84 = true ∨ valuation q 86 = true ∨ valuation q 89 = true := by
  rw [value84, value86, value88, value89, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(420 : Vertex), (424 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (492 : Vertex) [(420 : Vertex), (424 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 21 = false ∨ valuation q 85 = false ∨ valuation q 90 = false := by
  rw [value21, value85, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (422 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 21 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value21, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (428 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 205 = true ∨ valuation q 21 = true ∨ valuation q 88 = true ∨ valuation q 90 = true := by
  rw [value21, value88, value89, value90, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(174 : Vertex), (428 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (422 : Vertex) [(174 : Vertex), (428 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 22 = false ∨ valuation q 65 = false ∨ valuation q 89 = false := by
  rw [value22, value65, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (303 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 94 = false ∨ valuation q 97 = false := by
  rw [value25, value91, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 26 = false ∨ valuation q 84 = false ∨ valuation q 93 = false := by
  rw [value26, value84, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (180 : Vertex) (420 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 209 = true ∨ valuation q 92 = true := by
  rw [value92, value93, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(436 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (439 : Vertex) [(436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 210 = true ∨ valuation q 93 = true ∨ valuation q 98 = true := by
  rw [value93, value94, value98, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(437 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (435 : Vertex) [(437 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 210 = true ∨ valuation q 91 = true ∨ valuation q 98 = true := by
  rw [value91, value94, value98, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(435 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (437 : Vertex) [(435 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 210 = true ∨ valuation q 91 = true ∨ valuation q 93 = true := by
  rw [value91, value93, value94, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(435 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (447 : Vertex) [(435 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 211 = true ∨ valuation q 96 = true := by
  rw [value95, value96, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (424 : Vertex) [(442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 211 = true ∨ valuation q 86 = true := by
  rw [value86, value95, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(424 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (442 : Vertex) [(424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 212 = true ∨ valuation q 97 = true := by
  rw [value96, value97, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (442 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(443 : Vertex)] := by decide
  have hg := other_cover q (442 : Vertex) (440 : Vertex) [(443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 91 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value91, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (435 : Vertex) (442 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 213 = true ∨ valuation q 91 = true ∨ valuation q 98 = true := by
  rw [value91, value97, value98, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(435 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (442 : Vertex) [(435 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 90 = false ∨ valuation q 94 = false ∨ valuation q 97 = false := by
  rw [value90, value94, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (431 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 90 = false ∨ valuation q 94 = false ∨ valuation q 116 = false := by
  rw [value90, value94, value98, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (431 : Vertex) (439 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 32 = false ∨ valuation q 82 = false ∨ valuation q 100 = false := by
  rw [value32, value82, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (224 : Vertex) (416 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 32 = false ∨ valuation q 100 = false ∨ valuation q 108 = false := by
  rw [value32, value99, value100, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (224 : Vertex) (482 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 104 = false ∨ valuation q 110 = false := by
  rw [value100, value101, value104, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (483 : Vertex) (490 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 33 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value33, value100, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (482 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 33 = false ∨ valuation q 103 = false ∨ valuation q 105 = false := by
  rw [value33, value101, value103, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (487 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 105 = false := by
  rw [value100, value101, value103, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (482 : Vertex) (487 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E088.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112088
