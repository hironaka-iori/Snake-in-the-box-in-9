import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 52 = false ∨ valuation q 56 = false ∨ valuation q 58 = false := by
  rw [value52, value56, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (268 : Vertex) (280 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = true := by
  rw [value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ∈ [(284 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (285 : Vertex) [(284 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 58 = true := by
  rw [value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 63 = false := by
  rw [value59, value60, value61, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (322 : Vertex) (324 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 96 = false := by
  rw [value59, value60, value61, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (322 : Vertex) (324 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 63 = false ∨ valuation q 96 = false := by
  rw [value59, value60, value63, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (322 : Vertex) (328 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 178 = true ∨ valuation q 64 = true ∨ valuation q 98 = true := by
  rw [value60, value64, value98, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(330 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (320 : Vertex) [(330 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 178 = true ∨ valuation q 59 = true ∨ valuation q 98 = true := by
  rw [value59, value60, value98, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(320 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (330 : Vertex) [(320 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 178 = true ∨ valuation q 59 = true ∨ valuation q 64 = true := by
  rw [value59, value60, value64, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(320 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (450 : Vertex) [(320 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 179 = true ∨ valuation q 65 = true ∨ valuation q 68 = true ∨ valuation q 100 = true := by
  rw [value61, value65, value68, value100, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(332 : Vertex), (340 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (320 : Vertex) [(332 : Vertex), (340 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 179 = true ∨ valuation q 59 = true ∨ valuation q 68 = true ∨ valuation q 100 = true := by
  rw [value59, value61, value68, value100, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(320 : Vertex), (340 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (332 : Vertex) [(320 : Vertex), (340 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 180 = true ∨ valuation q 71 = true ∨ valuation q 101 = true := by
  rw [value62, value71, value101, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(343 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (71 : Vertex) [(343 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 180 = true ∨ valuation q 5 = true ∨ valuation q 101 = true := by
  rw [value5, value62, value101, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(71 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (343 : Vertex) [(71 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 180 = true ∨ valuation q 5 = true ∨ valuation q 71 = true := by
  rw [value5, value62, value71, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(71 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (455 : Vertex) [(71 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 59 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value59, value63, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (320 : Vertex) (330 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 64 = true ∨ valuation q 65 = true := by
  rw [value63, value64, value65, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(330 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (320 : Vertex) [(330 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 59 = true ∨ valuation q 65 = true := by
  rw [value59, value63, value65, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(320 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (330 : Vertex) [(320 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 59 = true ∨ valuation q 64 = true := by
  rw [value59, value63, value64, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(320 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (332 : Vertex) [(320 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 60 = false ∨ valuation q 63 = false ∨ valuation q 73 = false := by
  rw [value60, value63, value64, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (322 : Vertex) (328 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 66 = false := by
  rw [value61, value63, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (324 : Vertex) (328 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 104 = false := by
  rw [value61, value63, value65, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (324 : Vertex) (328 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 63 = false ∨ valuation q 66 = false ∨ valuation q 104 = false := by
  rw [value63, value65, value66, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (328 : Vertex) (333 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 184 = true ∨ valuation q 105 = true := by
  rw [value66, value105, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(461 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (332 : Vertex) [(461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 184 = true ∨ valuation q 65 = true := by
  rw [value65, value66, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(332 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (461 : Vertex) [(332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 12 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value12, value68, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (84 : Vertex) (341 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 61 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value61, value68, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (324 : Vertex) (341 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 61 = false ∨ valuation q 69 = false ∨ valuation q 111 = false := by
  rw [value61, value68, value69, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (324 : Vertex) (341 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 61 = false ∨ valuation q 70 = false ∨ valuation q 111 = false := by
  rw [value61, value68, value70, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (324 : Vertex) (342 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 111 = false := by
  rw [value68, value69, value70, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (341 : Vertex) (342 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 187 = true ∨ valuation q 68 = true ∨ valuation q 71 = true := by
  rw [value68, value69, value71, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(340 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (337 : Vertex) [(340 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 62 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value62, value69, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (327 : Vertex) (341 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 62 = false ∨ valuation q 69 = false ∨ valuation q 113 = false := by
  rw [value62, value69, value71, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (327 : Vertex) (341 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E096.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112096
