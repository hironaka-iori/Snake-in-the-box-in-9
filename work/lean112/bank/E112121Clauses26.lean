import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value96, value101, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value96, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value96, value106, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (441 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value96, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (442 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 101 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value101, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (435 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 101 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value101, value106, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (435 : Vertex) (441 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 101 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value101, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (435 : Vertex) (442 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value106, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (441 : Vertex) (442 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 235 = true ∨ valuation q 99 = true ∨ valuation q 104 = true ∨ valuation q 108 = true := by
  rw [value99, value104, value108, value109, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (191 : Vertex) → w ∈ [(431 : Vertex), (439 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (191 : Vertex) [(431 : Vertex), (439 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 235 = true ∨ valuation q 61 = true ∨ valuation q 104 = true ∨ valuation q 108 = true := by
  rw [value61, value104, value108, value109, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (431 : Vertex) → w ∈ [(191 : Vertex), (439 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (431 : Vertex) [(191 : Vertex), (439 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 235 = true ∨ valuation q 61 = true ∨ valuation q 99 = true ∨ valuation q 108 = true := by
  rw [value61, value99, value108, value109, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(191 : Vertex), (431 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (439 : Vertex) [(191 : Vertex), (431 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 235 = true ∨ valuation q 61 = true ∨ valuation q 99 = true ∨ valuation q 104 = true := by
  rw [value61, value99, value104, value109, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(191 : Vertex), (431 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (443 : Vertex) [(191 : Vertex), (431 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 236 = true ∨ valuation q 111 = true ∨ valuation q 114 = true := by
  rw [value110, value111, value114, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (416 : Vertex) → w ∈ [(481 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (416 : Vertex) [(481 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 236 = true ∨ valuation q 87 = true ∨ valuation q 114 = true := by
  rw [value87, value110, value114, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(416 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (481 : Vertex) [(416 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 236 = true ∨ valuation q 87 = true ∨ valuation q 111 = true := by
  rw [value87, value110, value111, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(416 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (488 : Vertex) [(416 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 88 = false ∨ valuation q 110 = false ∨ valuation q 115 = false := by
  rw [value88, value110, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (417 : Vertex) (480 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 88 = false ∨ valuation q 110 = false ∨ valuation q 119 = false := by
  rw [value88, value110, value111, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (417 : Vertex) (480 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 88 = false ∨ valuation q 115 = false ∨ valuation q 119 = false := by
  rw [value88, value111, value115, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (417 : Vertex) (489 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 110 = false ∨ valuation q 115 = false ∨ valuation q 119 = false := by
  rw [value110, value111, value115, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (480 : Vertex) (489 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 92 = false ∨ valuation q 113 = false ∨ valuation q 122 = false := by
  rw [value92, value112, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (422 : Vertex) (487 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 238 = true ∨ valuation q 113 = true ∨ valuation q 122 = true := by
  rw [value112, value113, value122, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(487 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (422 : Vertex) [(487 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 238 = true ∨ valuation q 92 = true ∨ valuation q 122 = true := by
  rw [value92, value112, value122, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(422 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (487 : Vertex) [(422 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 238 = true ∨ valuation q 92 = true ∨ valuation q 113 = true := by
  rw [value92, value112, value113, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(422 : Vertex), (487 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (502 : Vertex) [(422 : Vertex), (487 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 93 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value93, value112, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (423 : Vertex) (486 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 94 = false ∨ valuation q 110 = false ∨ valuation q 115 = false := by
  rw [value94, value110, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (480 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 240 = true ∨ valuation q 94 = true ∨ valuation q 115 = true := by
  rw [value94, value114, value115, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(424 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (480 : Vertex) [(424 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 96 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value96, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (427 : Vertex) (489 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 115 = false ∨ valuation q 118 = false ∨ valuation q 125 = false := by
  rw [value115, value117, value118, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (489 : Vertex) (495 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 99 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value99, value113, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (431 : Vertex) (487 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 113 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value113, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (487 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 244 = true ∨ valuation q 99 = true ∨ valuation q 113 = true ∨ valuation q 116 = true := by
  rw [value99, value113, value116, value118, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(431 : Vertex), (487 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (493 : Vertex) [(431 : Vertex), (487 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 100 = false ∨ valuation q 111 = false ∨ valuation q 121 = false := by
  rw [value100, value111, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (433 : Vertex) (481 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E121.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112121
