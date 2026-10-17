import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 122 = false := by
  rw [value103, value104, value105, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (440 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 103 = false ∨ valuation q 107 = false ∨ valuation q 122 = false := by
  rw [value103, value104, value107, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (440 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 107 = false ∨ valuation q 122 = false := by
  rw [value104, value105, value107, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (443 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 49 = false ∨ valuation q 93 = false ∨ valuation q 104 = false := by
  rw [value49, value93, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (187 : Vertex) (427 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 49 = false ∨ valuation q 93 = false ∨ valuation q 108 = false := by
  rw [value49, value93, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (187 : Vertex) (427 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 49 = false ∨ valuation q 101 = false ∨ valuation q 104 = false := by
  rw [value49, value101, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (187 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 49 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value49, value101, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (187 : Vertex) (435 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 84 = false ∨ valuation q 93 = false ∨ valuation q 101 = false := by
  rw [value84, value93, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (315 : Vertex) (427 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 84 = false ∨ valuation q 93 = false ∨ valuation q 104 = false := by
  rw [value84, value93, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (315 : Vertex) (427 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 84 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value84, value101, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (315 : Vertex) (435 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 93 = false ∨ valuation q 101 = false ∨ valuation q 104 = false := by
  rw [value93, value101, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 93 = false ∨ valuation q 104 = false ∨ valuation q 123 = false := by
  rw [value93, value104, value105, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (442 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 101 = false ∨ valuation q 104 = false ∨ valuation q 108 = false := by
  rw [value101, value104, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (435 : Vertex) (442 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 94 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value94, value102, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (444 : Vertex) (428 : Vertex) (436 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 94 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value94, value102, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (444 : Vertex) (428 : Vertex) (436 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 94 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value94, value103, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (444 : Vertex) (428 : Vertex) (440 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value102, value103, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (444 : Vertex) (436 : Vertex) (440 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 230 = true ∨ valuation q 94 = true ∨ valuation q 103 = true ∨ valuation q 107 = true := by
  rw [value94, value103, value106, value107, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(428 : Vertex), (440 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (436 : Vertex) [(428 : Vertex), (440 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 230 = true ∨ valuation q 94 = true ∨ valuation q 102 = true ∨ valuation q 103 = true := by
  rw [value94, value102, value103, value106, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(428 : Vertex), (436 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (446 : Vertex) [(428 : Vertex), (436 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 231 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 108 = true := by
  rw [value104, value106, value107, value108, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(442 : Vertex), (444 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (430 : Vertex) [(442 : Vertex), (444 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 231 = true ∨ valuation q 96 = true ∨ valuation q 106 = true ∨ valuation q 108 = true := by
  rw [value96, value106, value107, value108, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(430 : Vertex), (444 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (442 : Vertex) [(430 : Vertex), (444 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 231 = true ∨ valuation q 96 = true ∨ valuation q 104 = true ∨ valuation q 108 = true := by
  rw [value96, value104, value107, value108, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (444 : Vertex) → w ∈ [(430 : Vertex), (442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (444 : Vertex) [(430 : Vertex), (442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 231 = true ∨ valuation q 96 = true ∨ valuation q 104 = true ∨ valuation q 106 = true := by
  rw [value96, value104, value106, value107, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(430 : Vertex), (442 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (447 : Vertex) [(430 : Vertex), (442 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 51 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value51, value97, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (191 : Vertex) (431 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 51 = false ∨ valuation q 97 = false ∨ valuation q 107 = false := by
  rw [value51, value97, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (191 : Vertex) (431 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 51 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value51, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (191 : Vertex) (443 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 97 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value97, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (431 : Vertex) (443 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 232 = true ∨ valuation q 51 = true ∨ valuation q 105 = true ∨ valuation q 107 = true := by
  rw [value51, value105, value107, value108, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (431 : Vertex) → w ∈ [(191 : Vertex), (443 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (431 : Vertex) [(191 : Vertex), (443 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 232 = true ∨ valuation q 51 = true ∨ valuation q 97 = true ∨ valuation q 105 = true := by
  rw [value51, value97, value105, value108, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(191 : Vertex), (431 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (446 : Vertex) [(191 : Vertex), (431 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 86 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value86, value109, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (416 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 86 = false ∨ valuation q 110 = false := by
  rw [value86, value110, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (480 : Vertex) (416 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide)

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value110, value113, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (480 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E008.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112008
