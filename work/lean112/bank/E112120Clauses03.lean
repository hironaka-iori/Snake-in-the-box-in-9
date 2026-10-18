import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 47 = false ∨ valuation q 59 = false ∨ valuation q 94 = false := by
  rw [value47, value57, value59, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (283 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 56 = false ∨ valuation q 59 = false ∨ valuation q 94 = false := by
  rw [value56, value57, value59, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (280 : Vertex) (283 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 48 = false ∨ valuation q 56 = false ∨ valuation q 59 = false := by
  rw [value48, value56, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (266 : Vertex) (280 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 48 = false ∨ valuation q 56 = false ∨ valuation q 72 = false := by
  rw [value48, value56, value58, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (266 : Vertex) (280 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 48 = false ∨ valuation q 56 = false ∨ valuation q 95 = false := by
  rw [value48, value56, value58, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (266 : Vertex) (280 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 48 = false ∨ valuation q 59 = false ∨ valuation q 72 = false := by
  rw [value48, value58, value59, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (266 : Vertex) (283 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 48 = false ∨ valuation q 59 = false ∨ valuation q 95 = false := by
  rw [value48, value58, value59, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (266 : Vertex) (283 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 56 = false ∨ valuation q 59 = false ∨ valuation q 72 = false := by
  rw [value56, value58, value59, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (280 : Vertex) (283 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 56 = false ∨ valuation q 59 = false ∨ valuation q 95 = false := by
  rw [value56, value58, value59, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (280 : Vertex) (283 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 175 = true ∨ valuation q 49 = true ∨ valuation q 57 = true ∨ valuation q 58 = true := by
  rw [value49, value57, value58, value59, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(267 : Vertex), (281 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (287 : Vertex) [(267 : Vertex), (281 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 176 = true ∨ valuation q 59 = true := by
  rw [value59, value60, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(283 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (279 : Vertex) [(283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 177 = true ∨ valuation q 62 = true := by
  rw [value61, value62, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(321 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (328 : Vertex) [(321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 178 = true ∨ valuation q 65 = true ∨ valuation q 68 = true := by
  rw [value62, value65, value68, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(329 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(329 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 179 = true := by
  rw [value63, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (327 : Vertex) (335 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 180 = true ∨ valuation q 61 = true ∨ valuation q 65 = true := by
  rw [value61, value64, value65, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(320 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (72 : Vertex) [(320 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 47 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value47, value62, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (265 : Vertex) (321 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 47 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value47, value62, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (265 : Vertex) (321 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 47 = false ∨ valuation q 62 = false ∨ valuation q 103 = false := by
  rw [value47, value62, value65, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (265 : Vertex) (321 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 47 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value47, value64, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (265 : Vertex) (328 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 47 = false ∨ valuation q 64 = false ∨ valuation q 103 = false := by
  rw [value47, value64, value65, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (265 : Vertex) (328 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 47 = false ∨ valuation q 66 = false ∨ valuation q 103 = false := by
  rw [value47, value65, value66, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (265 : Vertex) (333 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 62 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value62, value64, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (328 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 182 = true ∨ valuation q 67 = true ∨ valuation q 74 = true := by
  rw [value66, value67, value74, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(335 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (329 : Vertex) [(335 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 182 = true ∨ valuation q 65 = true ∨ valuation q 67 = true := by
  rw [value65, value66, value67, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(329 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (349 : Vertex) [(329 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 63 = true ∨ valuation q 66 = true := by
  rw [value63, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ∈ [(327 : Vertex), (333 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (335 : Vertex) [(327 : Vertex), (333 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 183 = true ∨ valuation q 63 = true := by
  rw [value63, value67, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(327 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (333 : Vertex) [(327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 184 = true ∨ valuation q 70 = true := by
  rw [value68, value70, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(339 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (321 : Vertex) [(339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 184 = true ∨ valuation q 62 = true := by
  rw [value62, value68, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(321 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (339 : Vertex) [(321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value69, value70, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (339 : Vertex) (342 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 185 = true ∨ valuation q 71 = true ∨ valuation q 72 = true := by
  rw [value69, value71, value72, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(342 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (339 : Vertex) [(342 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 185 = true ∨ valuation q 70 = true ∨ valuation q 71 = true := by
  rw [value69, value70, value71, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(339 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (346 : Vertex) [(339 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 186 = true ∨ valuation q 69 = true := by
  rw [value69, value70, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(338 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (337 : Vertex) [(338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E120.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112120
