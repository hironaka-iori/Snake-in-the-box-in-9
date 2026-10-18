import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 233 = true ∨ valuation q 86 = true ∨ valuation q 113 = true := by
  rw [value86, value109, value113, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(416 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (481 : Vertex) [(416 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 233 = true ∨ valuation q 86 = true ∨ valuation q 110 = true := by
  rw [value86, value109, value110, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(416 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (488 : Vertex) [(416 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 234 = true ∨ valuation q 109 = true ∨ valuation q 114 = true := by
  rw [value109, value110, value114, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(480 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (417 : Vertex) [(480 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 234 = true ∨ valuation q 87 = true ∨ valuation q 114 = true := by
  rw [value87, value110, value114, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(417 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (480 : Vertex) [(417 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 234 = true ∨ valuation q 87 = true ∨ valuation q 109 = true := by
  rw [value87, value109, value110, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(417 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (489 : Vertex) [(417 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 116 = true := by
  rw [value111, value116, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(494 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (487 : Vertex) [(494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 112 = true := by
  rw [value111, value112, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (494 : Vertex) → w ∈ [(487 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (494 : Vertex) [(487 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 55 = false ∨ valuation q 111 = false ∨ valuation q 120 = false := by
  rw [value55, value111, value112, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (231 : Vertex) (486 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 55 = true ∨ valuation q 91 = true ∨ valuation q 120 = true := by
  rw [value55, value91, value112, value120, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(231 : Vertex), (423 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (486 : Vertex) [(231 : Vertex), (423 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 55 = true ∨ valuation q 91 = true ∨ valuation q 111 = true := by
  rw [value55, value91, value111, value112, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(231 : Vertex), (423 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (503 : Vertex) [(231 : Vertex), (423 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 92 = false ∨ valuation q 109 = false ∨ valuation q 115 = false := by
  rw [value92, value109, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (480 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 92 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value92, value113, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (489 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 92 = true ∨ valuation q 114 = true ∨ valuation q 115 = true := by
  rw [value92, value113, value114, value115, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(424 : Vertex), (489 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (480 : Vertex) [(424 : Vertex), (489 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 92 = true ∨ valuation q 109 = true ∨ valuation q 114 = true := by
  rw [value92, value109, value113, value114, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(424 : Vertex), (480 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (492 : Vertex) [(424 : Vertex), (480 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 56 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value56, value110, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 56 = false ∨ valuation q 110 = false ∨ valuation q 121 = false := by
  rw [value56, value110, value114, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (481 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 56 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value56, value113, value114, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (488 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 110 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value110, value113, value114, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (488 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 94 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value94, value113, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (428 : Vertex) (488 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 239 = true ∨ valuation q 113 = true ∨ valuation q 116 = true := by
  rw [value113, value115, value116, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(488 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (428 : Vertex) [(488 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 239 = true ∨ valuation q 94 = true ∨ valuation q 116 = true := by
  rw [value94, value115, value116, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(428 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (488 : Vertex) [(428 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 239 = true ∨ valuation q 94 = true ∨ valuation q 113 = true := by
  rw [value94, value113, value115, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (494 : Vertex) → w ∈ [(428 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (494 : Vertex) [(428 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 240 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value111, value115, value116, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (494 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(486 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (494 : Vertex) (430 : Vertex) [(486 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 240 = true ∨ valuation q 96 = true ∨ valuation q 115 = true := by
  rw [value96, value115, value116, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (494 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(430 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (494 : Vertex) (486 : Vertex) [(430 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 240 = true ∨ valuation q 96 = true ∨ valuation q 111 = true := by
  rw [value96, value111, value116, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (494 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(430 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (494 : Vertex) (492 : Vertex) [(430 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 63 = false ∨ valuation q 100 = false ∨ valuation q 122 = false := by
  rw [value63, value100, value117, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (434 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 63 = false ∨ valuation q 122 = false := by
  rw [value63, value122, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (498 : Vertex) (242 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide)

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 241 = true ∨ valuation q 63 = true ∨ valuation q 100 = true := by
  rw [value63, value100, value117, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(242 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (506 : Vertex) [(242 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 65 = false ∨ valuation q 102 = false ∨ valuation q 119 = false := by
  rw [value65, value102, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (244 : Vertex) (436 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 102 = true ∨ valuation q 119 = true := by
  rw [value102, value118, value119, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(436 : Vertex), (501 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (244 : Vertex) [(436 : Vertex), (501 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 65 = true ∨ valuation q 102 = true := by
  rw [value65, value102, value118, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (501 : Vertex) → w ∈ [(244 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (501 : Vertex) [(244 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 118 = false ∨ valuation q 120 = false ∨ valuation q 124 = false := by
  rw [value118, value119, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (500 : Vertex) (503 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E008.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112008
