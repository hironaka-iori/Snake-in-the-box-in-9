import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 237 = true ∨ valuation q 97 = true ∨ valuation q 102 = true ∨ valuation q 107 = true ∨ valuation q 110 = true := by
  rw [value97, value102, value107, value109, value110, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex), (441 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (442 : Vertex) [(427 : Vertex), (435 : Vertex), (441 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 237 = true ∨ valuation q 97 = true ∨ valuation q 102 = true ∨ valuation q 107 = true ∨ valuation q 108 = true := by
  rw [value97, value102, value107, value108, value109, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (447 : Vertex) [(427 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 50 = false ∨ valuation q 100 = false ∨ valuation q 105 = false := by
  rw [value50, value100, value105, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (191 : Vertex) (431 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 50 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value50, value100, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (191 : Vertex) (431 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 50 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value50, value105, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (191 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 100 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value100, value105, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (431 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 238 = true ∨ valuation q 50 = true ∨ valuation q 100 = true ∨ valuation q 109 = true := by
  rw [value50, value100, value109, value110, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(191 : Vertex), (431 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (439 : Vertex) [(191 : Vertex), (431 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 238 = true ∨ valuation q 50 = true ∨ valuation q 100 = true ∨ valuation q 105 = true := by
  rw [value50, value100, value105, value110, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(191 : Vertex), (431 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (443 : Vertex) [(191 : Vertex), (431 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 88 = false ∨ valuation q 112 = false ∨ valuation q 115 = false := by
  rw [value88, value111, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (416 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 88 = false ∨ valuation q 115 = false := by
  rw [value88, value115, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (480 : Vertex) (416 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide)

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 112 = false ∨ valuation q 115 = false := by
  rw [value112, value115, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (480 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide)

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 239 = true ∨ valuation q 88 = true ∨ valuation q 115 = true := by
  rw [value88, value111, value115, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(416 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (481 : Vertex) [(416 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 239 = true ∨ valuation q 88 = true ∨ valuation q 112 = true := by
  rw [value88, value111, value112, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(416 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (488 : Vertex) [(416 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 89 = false ∨ valuation q 111 = false ∨ valuation q 120 = false := by
  rw [value89, value111, value112, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (417 : Vertex) (480 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 89 = false ∨ valuation q 116 = false ∨ valuation q 120 = false := by
  rw [value89, value112, value116, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (417 : Vertex) (489 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 240 = true ∨ valuation q 89 = true ∨ valuation q 116 = true ∨ valuation q 120 = true := by
  rw [value89, value112, value116, value120, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(417 : Vertex), (489 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (480 : Vertex) [(417 : Vertex), (489 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 240 = true ∨ valuation q 89 = true ∨ valuation q 111 = true ∨ valuation q 120 = true := by
  rw [value89, value111, value112, value120, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(417 : Vertex), (480 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (489 : Vertex) [(417 : Vertex), (480 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 240 = true ∨ valuation q 89 = true ∨ valuation q 111 = true ∨ valuation q 116 = true := by
  rw [value89, value111, value112, value116, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(417 : Vertex), (480 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (497 : Vertex) [(417 : Vertex), (480 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 55 = false ∨ valuation q 93 = false ∨ valuation q 114 = false := by
  rw [value55, value93, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (422 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 55 = false ∨ valuation q 93 = false ∨ valuation q 124 = false := by
  rw [value55, value93, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (422 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 93 = false ∨ valuation q 114 = false ∨ valuation q 124 = false := by
  rw [value93, value113, value114, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (422 : Vertex) (487 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 241 = true ∨ valuation q 93 = true ∨ valuation q 114 = true ∨ valuation q 124 = true := by
  rw [value93, value113, value114, value124, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [(422 : Vertex), (487 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (230 : Vertex) [(422 : Vertex), (487 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 241 = true ∨ valuation q 55 = true ∨ valuation q 93 = true ∨ valuation q 124 = true := by
  rw [value55, value93, value113, value124, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(230 : Vertex), (422 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (487 : Vertex) [(230 : Vertex), (422 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 94 = false ∨ valuation q 113 = false ∨ valuation q 119 = false := by
  rw [value94, value113, value114, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (423 : Vertex) (486 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 242 = true ∨ valuation q 113 = true ∨ valuation q 119 = true := by
  rw [value113, value114, value119, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(486 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (423 : Vertex) [(486 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 242 = true ∨ valuation q 94 = true ∨ valuation q 119 = true := by
  rw [value94, value114, value119, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(423 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (486 : Vertex) [(423 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 242 = true ∨ valuation q 94 = true ∨ valuation q 113 = true := by
  rw [value94, value113, value114, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(423 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (495 : Vertex) [(423 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 95 = false ∨ valuation q 111 = false ∨ valuation q 116 = false := by
  rw [value95, value111, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (480 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 111 = true ∨ valuation q 116 = true := by
  rw [value111, value115, value116, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(480 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (424 : Vertex) [(480 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 95 = true ∨ valuation q 116 = true := by
  rw [value95, value115, value116, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(424 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (480 : Vertex) [(424 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 95 = true ∨ valuation q 111 = true := by
  rw [value95, value111, value115, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(424 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (489 : Vertex) [(424 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 56 = false ∨ valuation q 112 = false ∨ valuation q 115 = false := by
  rw [value56, value112, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E036.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112036
