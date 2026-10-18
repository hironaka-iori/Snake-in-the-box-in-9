import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 165 = true ∨ valuation q 54 = true ∨ valuation q 60 = true := by
  rw [value54, value55, value60, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(276 : Vertex), (285 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (279 : Vertex) [(276 : Vertex), (285 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 166 = true ∨ valuation q 55 = true ∨ valuation q 61 = true := by
  rw [value55, value56, value61, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(277 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (263 : Vertex) [(277 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 166 = true ∨ valuation q 47 = true ∨ valuation q 61 = true := by
  rw [value47, value56, value61, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(263 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (277 : Vertex) [(263 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 166 = true ∨ valuation q 47 = true ∨ valuation q 55 = true := by
  rw [value47, value55, value56, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(263 : Vertex), (277 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (287 : Vertex) [(263 : Vertex), (277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 49 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value49, value57, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (283 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 167 = true ∨ valuation q 59 = true ∨ valuation q 60 = true := by
  rw [value57, value59, value60, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(283 : Vertex), (285 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (265 : Vertex) [(283 : Vertex), (285 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 167 = true ∨ valuation q 49 = true ∨ valuation q 60 = true := by
  rw [value49, value57, value60, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(265 : Vertex), (285 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (283 : Vertex) [(265 : Vertex), (285 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 167 = true ∨ valuation q 49 = true ∨ valuation q 59 = true := by
  rw [value49, value57, value59, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (285 : Vertex) → w ∈ [(265 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (285 : Vertex) [(265 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 10 = false ∨ valuation q 50 = false ∨ valuation q 59 = false := by
  rw [value10, value50, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (26 : Vertex) (266 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 50 = false ∨ valuation q 59 = false ∨ valuation q 75 = false := by
  rw [value50, value58, value59, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (266 : Vertex) (283 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 61 = false := by
  rw [value57, value58, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (281 : Vertex) (282 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 169 = true ∨ valuation q 58 = true ∨ valuation q 61 = true := by
  rw [value58, value59, value61, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(282 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (281 : Vertex) [(282 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 169 = true ∨ valuation q 57 = true ∨ valuation q 61 = true := by
  rw [value57, value59, value61, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(281 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (282 : Vertex) [(281 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 169 = true ∨ valuation q 57 = true ∨ valuation q 58 = true := by
  rw [value57, value58, value59, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(281 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (287 : Vertex) [(281 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 12 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value12, value55, value57, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (285 : Vertex) (29 : Vertex) (277 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 12 = false ∨ valuation q 55 = false ∨ valuation q 77 = false := by
  rw [value12, value55, value60, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (285 : Vertex) (29 : Vertex) (277 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 12 = false ∨ valuation q 57 = false ∨ valuation q 77 = false := by
  rw [value12, value57, value60, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (285 : Vertex) (29 : Vertex) (281 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 12 = false ∨ valuation q 61 = false ∨ valuation q 77 = false := by
  rw [value12, value60, value61, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (285 : Vertex) (29 : Vertex) (287 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 77 = false := by
  rw [value55, value57, value60, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (285 : Vertex) (277 : Vertex) (281 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 56 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value56, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (283 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 171 = true ∨ valuation q 59 = true ∨ valuation q 60 = true := by
  rw [value59, value60, value61, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(283 : Vertex), (285 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (279 : Vertex) [(283 : Vertex), (285 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 43 = false ∨ valuation q 63 = false ∨ valuation q 67 = false := by
  rw [value43, value62, value63, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (256 : Vertex) (321 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 172 = true ∨ valuation q 43 = true ∨ valuation q 67 = true := by
  rw [value43, value62, value67, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(256 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (321 : Vertex) [(256 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 62 = false ∨ valuation q 64 = false ∨ valuation q 71 = false := by
  rw [value62, value63, value64, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (320 : Vertex) (325 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 68 = false ∨ valuation q 71 = false := by
  rw [value63, value64, value68, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (325 : Vertex) (329 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 173 = true ∨ valuation q 64 = true ∨ valuation q 68 = true ∨ valuation q 71 = true := by
  rw [value63, value64, value68, value71, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(325 : Vertex), (329 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(325 : Vertex), (329 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 173 = true ∨ valuation q 62 = true ∨ valuation q 64 = true ∨ valuation q 68 = true := by
  rw [value62, value63, value64, value68, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(320 : Vertex), (325 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (337 : Vertex) [(320 : Vertex), (325 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 63 = false ∨ valuation q 66 = false ∨ valuation q 69 = false := by
  rw [value63, value64, value66, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (321 : Vertex) (327 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 46 = false ∨ valuation q 66 = false ∨ valuation q 74 = false := by
  rw [value46, value65, value66, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (262 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 46 = false ∨ valuation q 66 = false ∨ valuation q 97 = false := by
  rw [value46, value65, value66, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (262 : Vertex) (327 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 46 = false ∨ valuation q 74 = false ∨ valuation q 97 = false := by
  rw [value46, value65, value74, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (262 : Vertex) (342 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 74 = false ∨ valuation q 97 = false := by
  rw [value65, value66, value74, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (327 : Vertex) (342 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E107.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112107
