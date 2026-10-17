import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 170 = true ∨ valuation q 56 = true ∨ valuation q 63 = true := by
  rw [value54, value56, value63, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (298 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(302 : Vertex), (314 : Vertex)] := by decide
  have hg := other_cover q (298 : Vertex) (296 : Vertex) [(302 : Vertex), (314 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 170 = true ∨ valuation q 53 = true ∨ valuation q 56 = true := by
  rw [value53, value54, value56, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (298 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(296 : Vertex), (302 : Vertex)] := by decide
  have hg := other_cover q (298 : Vertex) (314 : Vertex) [(296 : Vertex), (302 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 171 = true ∨ valuation q 56 = true ∨ valuation q 94 = true := by
  rw [value55, value56, value94, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (300 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(302 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (300 : Vertex) (296 : Vertex) [(302 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 171 = true ∨ valuation q 53 = true ∨ valuation q 56 = true := by
  rw [value53, value55, value56, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (300 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(296 : Vertex), (302 : Vertex)] := by decide
  have hg := other_cover q (300 : Vertex) (428 : Vertex) [(296 : Vertex), (302 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value51, value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (294 : Vertex) (298 : Vertex) (300 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 74 = false := by
  rw [value51, value54, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (294 : Vertex) (298 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 74 = false := by
  rw [value51, value55, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (294 : Vertex) (300 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 74 = false := by
  rw [value54, value55, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (298 : Vertex) (300 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 54 = false ∨ valuation q 57 = false ∨ valuation q 74 = false := by
  rw [value54, value56, value57, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (298 : Vertex) (303 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 74 = false := by
  rw [value55, value56, value57, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (300 : Vertex) (303 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 52 = false ∨ valuation q 75 = false ∨ valuation q 96 = false := by
  rw [value52, value57, value75, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (367 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 56 = false ∨ valuation q 75 = false ∨ valuation q 96 = false := by
  rw [value56, value57, value75, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (302 : Vertex) (367 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 173 = true ∨ valuation q 56 = true ∨ valuation q 75 = true ∨ valuation q 96 = true := by
  rw [value56, value57, value75, value96, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (303 : Vertex) w → w ∈ region → w ≠ (295 : Vertex) → w ∈ [(302 : Vertex), (367 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (303 : Vertex) (295 : Vertex) [(302 : Vertex), (367 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 173 = true ∨ valuation q 52 = true ∨ valuation q 75 = true ∨ valuation q 96 = true := by
  rw [value52, value57, value75, value96, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (303 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(295 : Vertex), (367 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (303 : Vertex) (302 : Vertex) [(295 : Vertex), (367 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 174 = true ∨ valuation q 60 = true ∨ valuation q 62 = true := by
  rw [value58, value60, value62, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(309 : Vertex), (313 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (289 : Vertex) [(309 : Vertex), (313 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 174 = true ∨ valuation q 50 = true ∨ valuation q 60 = true := by
  rw [value50, value58, value60, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (313 : Vertex) → w ∈ [(289 : Vertex), (309 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (313 : Vertex) [(289 : Vertex), (309 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 175 = true ∨ valuation q 60 = true ∨ valuation q 100 = true := by
  rw [value59, value60, value100, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (308 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(309 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (308 : Vertex) (310 : Vertex) [(309 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 175 = true ∨ valuation q 60 = true ∨ valuation q 61 = true := by
  rw [value59, value60, value61, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (308 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(309 : Vertex), (310 : Vertex)] := by decide
  have hg := other_cover q (308 : Vertex) (436 : Vertex) [(309 : Vertex), (310 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 65 = false := by
  rw [value58, value59, value60, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (309 : Vertex) (305 : Vertex) (308 : Vertex) (317 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 59 = false ∨ valuation q 101 = false := by
  rw [value51, value59, value61, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (310 : Vertex) (294 : Vertex) (308 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 177 = true ∨ valuation q 59 = true ∨ valuation q 101 = true := by
  rw [value59, value61, value101, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(308 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (294 : Vertex) [(308 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 177 = true ∨ valuation q 51 = true ∨ valuation q 101 = true := by
  rw [value51, value61, value101, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(294 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (308 : Vertex) [(294 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 58 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value58, value62, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (313 : Vertex) (305 : Vertex) (315 : Vertex) (317 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 179 = true ∨ valuation q 64 = true ∨ valuation q 80 = true := by
  rw [value63, value64, value80, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (298 : Vertex) → w ∈ [(315 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (298 : Vertex) [(315 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 179 = true ∨ valuation q 54 = true ∨ valuation q 80 = true := by
  rw [value54, value63, value80, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (315 : Vertex) → w ∈ [(298 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (315 : Vertex) [(298 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 180 = true ∨ valuation q 63 = true := by
  rw [value63, value64, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (315 : Vertex) w → w ∈ region → w ≠ (313 : Vertex) → w ∈ [(314 : Vertex)] := by decide
  have hg := other_cover q (315 : Vertex) (313 : Vertex) [(314 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 180 = true ∨ valuation q 62 = true := by
  rw [value62, value64, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (315 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(313 : Vertex)] := by decide
  have hg := other_cover q (315 : Vertex) (314 : Vertex) [(313 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 60 = false ∨ valuation q 62 = false ∨ valuation q 82 = false := by
  rw [value60, value62, value65, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (317 : Vertex) (309 : Vertex) (313 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 22 = false ∨ valuation q 50 = false ∨ valuation q 68 = false := by
  rw [value22, value50, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (97 : Vertex) (289 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 22 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value22, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (97 : Vertex) (352 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 72 = false := by
  rw [value67, value68, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (353 : Vertex) (359 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 78 = false := by
  rw [value67, value68, value70, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (353 : Vertex) (359 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E051.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112051
