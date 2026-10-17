import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value48, value51, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 74 = false := by
  rw [value48, value51, value53, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (299 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 74 = false := by
  rw [value48, value52, value53, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (301 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 74 = false := by
  rw [value51, value52, value53, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (299 : Vertex) (301 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 46 = false ∨ valuation q 56 = false ∨ valuation q 75 = false := by
  rw [value46, value54, value56, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (289 : Vertex) (307 : Vertex) (369 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 58 = false := by
  rw [value55, value56, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (307 : Vertex) (310 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 172 = true ∨ valuation q 55 = true ∨ valuation q 76 = true := by
  rw [value55, value56, value76, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(306 : Vertex), (371 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(306 : Vertex), (371 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 172 = true ∨ valuation q 54 = true ∨ valuation q 76 = true := by
  rw [value54, value56, value76, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(305 : Vertex), (371 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (306 : Vertex) [(305 : Vertex), (371 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 47 = false ∨ valuation q 55 = false ∨ valuation q 61 = false := by
  rw [value47, value55, value57, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (310 : Vertex) (294 : Vertex) (306 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 173 = true ∨ valuation q 47 = true ∨ valuation q 55 = true := by
  rw [value47, value55, value57, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(294 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (318 : Vertex) [(294 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 174 = true ∨ valuation q 55 = true ∨ valuation q 81 = true := by
  rw [value55, value58, value81, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(306 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (318 : Vertex) [(306 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 175 = true ∨ valuation q 61 = true := by
  rw [value59, value61, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(318 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (317 : Vertex) [(318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value57, value58, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (310 : Vertex) (314 : Vertex) (316 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 2 = false ∨ valuation q 46 = false ∨ valuation q 62 = false := by
  rw [value2, value46, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (97 : Vertex) (289 : Vertex) (352 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 2 = false ∨ valuation q 46 = false ∨ valuation q 75 = false := by
  rw [value2, value46, value63, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (97 : Vertex) (289 : Vertex) (369 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 2 = false ∨ valuation q 62 = false ∨ valuation q 101 = false := by
  rw [value2, value62, value63, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (97 : Vertex) (352 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 46 = false ∨ valuation q 62 = false ∨ valuation q 101 = false := by
  rw [value46, value62, value63, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (289 : Vertex) (352 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 46 = false ∨ valuation q 66 = false ∨ valuation q 75 = false := by
  rw [value46, value63, value66, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (289 : Vertex) (357 : Vertex) (369 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 46 = false ∨ valuation q 66 = false ∨ valuation q 101 = false := by
  rw [value46, value63, value66, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (289 : Vertex) (357 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 75 = false := by
  rw [value62, value63, value66, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (352 : Vertex) (357 : Vertex) (369 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 101 = false := by
  rw [value62, value63, value66, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (352 : Vertex) (357 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 62 = false ∨ valuation q 75 = false ∨ valuation q 101 = false := by
  rw [value62, value63, value75, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (352 : Vertex) (369 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 66 = false ∨ valuation q 75 = false ∨ valuation q 101 = false := by
  rw [value63, value66, value75, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (357 : Vertex) (369 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 62 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value62, value64, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (354 : Vertex) (352 : Vertex) (358 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value62, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (352 : Vertex) (357 : Vertex) (358 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 72 = false := by
  rw [value62, value65, value66, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (352 : Vertex) (357 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 62 = false ∨ valuation q 67 = false ∨ valuation q 72 = false := by
  rw [value62, value65, value67, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (352 : Vertex) (358 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 62 = false ∨ valuation q 67 = false ∨ valuation q 77 = false := by
  rw [value62, value65, value67, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (352 : Vertex) (358 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 62 = false ∨ valuation q 72 = false ∨ valuation q 77 = false := by
  rw [value62, value65, value72, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (352 : Vertex) (364 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 72 = false := by
  rw [value65, value66, value67, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (357 : Vertex) (358 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 72 = false ∨ valuation q 77 = false := by
  rw [value65, value67, value72, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (358 : Vertex) (364 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 181 = true ∨ valuation q 62 = true ∨ valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 72 = true := by
  rw [value62, value65, value66, value67, value72, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (356 : Vertex) w → w ∈ region → w ≠ (372 : Vertex) → w ∈ [(352 : Vertex), (357 : Vertex), (358 : Vertex), (364 : Vertex)] := by decide
  have hg := other_cover q (356 : Vertex) (372 : Vertex) [(352 : Vertex), (357 : Vertex), (358 : Vertex), (364 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E058.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112058
