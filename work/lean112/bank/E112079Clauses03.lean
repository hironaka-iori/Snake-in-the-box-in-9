import E112079Semantics
import B112E079Inputs
namespace Snake9.Regrowth.E112079
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 79 = false := by
  rw [value58, value61, value63, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (291 : Vertex) (307 : Vertex) (355 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 171 = true ∨ valuation q 58 = true := by
  rw [value58, value61, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(291 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(291 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 173 = true ∨ valuation q 58 = true ∨ valuation q 67 = true := by
  rw [value58, value63, value67, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (354 : Vertex) → w ∈ [(291 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (354 : Vertex) [(291 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 71 = false := by
  rw [value64, value65, value68, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (357 : Vertex) (364 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 64 = true ∨ valuation q 72 = true := by
  rw [value64, value65, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ∈ [(356 : Vertex), (373 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (357 : Vertex) [(356 : Vertex), (373 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 63 = false ∨ valuation q 66 = false ∨ valuation q 76 = false := by
  rw [value63, value66, value67, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 59 = false ∨ valuation q 71 = false ∨ valuation q 74 = false := by
  rw [value59, value70, value71, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (304 : Vertex) (372 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 65 = false ∨ valuation q 71 = false ∨ valuation q 73 = false := by
  rw [value65, value71, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (357 : Vertex) (372 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 183 = true ∨ valuation q 77 = true := by
  rw [value73, value77, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(383 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (373 : Vertex) [(383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 70 = true ∨ valuation q 75 = true := by
  rw [value70, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ∈ [(368 : Vertex), (377 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (376 : Vertex) [(368 : Vertex), (377 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 184 = true ∨ valuation q 70 = true := by
  rw [value70, value74, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(368 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (377 : Vertex) [(368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 67 = false ∨ valuation q 75 = false ∨ valuation q 77 = false := by
  rw [value67, value75, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (363 : Vertex) (377 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 188 = true ∨ valuation q 79 = true ∨ valuation q 82 = true := by
  rw [value78, value79, value82, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (162 : Vertex) → w ∈ [(419 : Vertex), (426 : Vertex)] := by decide
  have hg := other_cover q (418 : Vertex) (162 : Vertex) [(419 : Vertex), (426 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 188 = true ∨ valuation q 17 = true ∨ valuation q 79 = true := by
  rw [value17, value78, value79, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(162 : Vertex), (419 : Vertex)] := by decide
  have hg := other_cover q (418 : Vertex) (426 : Vertex) [(162 : Vertex), (419 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 58 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value58, value78, value79, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (291 : Vertex) (418 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 189 = true ∨ valuation q 18 = true ∨ valuation q 78 = true ∨ valuation q 83 = true := by
  rw [value18, value78, value79, value83, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (291 : Vertex) → w ∈ [(163 : Vertex), (418 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (291 : Vertex) [(163 : Vertex), (418 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value80, value81, value84, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 19 = false ∨ valuation q 80 = false ∨ valuation q 88 = false := by
  rw [value19, value80, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (420 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 78 = false ∨ valuation q 83 = false ∨ valuation q 92 = false := by
  rw [value78, value82, value83, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (418 : Vertex) (427 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 78 = false ∨ valuation q 85 = false ∨ valuation q 92 = false := by
  rw [value78, value82, value85, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (418 : Vertex) (430 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 192 = true ∨ valuation q 78 = true ∨ valuation q 83 = true ∨ valuation q 92 = true := by
  rw [value78, value82, value83, value92, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(418 : Vertex), (427 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (430 : Vertex) [(418 : Vertex), (427 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 21 = false ∨ valuation q 79 = false ∨ valuation q 93 = false := by
  rw [value21, value79, value83, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (419 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 21 = false ∨ valuation q 82 = false ∨ valuation q 93 = false := by
  rw [value21, value82, value83, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 93 = false ∨ valuation q 99 = false := by
  rw [value82, value83, value93, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (426 : Vertex) (443 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 194 = true ∨ valuation q 85 = true := by
  rw [value84, value85, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(430 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (420 : Vertex) [(430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 194 = true ∨ valuation q 80 = true := by
  rw [value80, value84, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(420 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (430 : Vertex) [(420 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 195 = true ∨ valuation q 82 = true := by
  rw [value82, value85, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(426 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (428 : Vertex) [(426 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 24 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value24, value86, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (176 : Vertex) (436 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 80 = false ∨ valuation q 88 = false ∨ valuation q 105 = false := by
  rw [value80, value87, value88, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (420 : Vertex) (437 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 197 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 105 = true := by
  rw [value86, value87, value88, value105, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(432 : Vertex), (437 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (420 : Vertex) [(432 : Vertex), (437 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 81 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value81, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (436 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 198 = true ∨ valuation q 81 = true ∨ valuation q 89 = true := by
  rw [value81, value88, value89, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(421 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (436 : Vertex) [(421 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E079.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112079
