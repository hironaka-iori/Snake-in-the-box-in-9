import E112201Semantics
import B112E201Inputs
namespace Snake9.Regrowth.E112201
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 154 = true ∨ valuation q 47 = true := by
  rw [value45, value47, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (291 : Vertex) → w ∈ [(267 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (291 : Vertex) [(267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 46 = true := by
  rw [value46, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (261 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 50 = true := by
  rw [value46, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ∈ [(277 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (261 : Vertex) [(277 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 155 = true := by
  rw [value46, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (261 : Vertex) (277 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 3 = false ∨ valuation q 45 = false ∨ valuation q 53 = false := by
  rw [value3, value45, value47, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (259 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 157 = true ∨ valuation q 57 = true := by
  rw [value48, value57, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(304 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (276 : Vertex) [(304 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 157 = true ∨ valuation q 49 = true := by
  rw [value48, value49, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (304 : Vertex) → w ∈ [(276 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (304 : Vertex) [(276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 158 = true ∨ valuation q 50 = true := by
  rw [value49, value50, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(277 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (272 : Vertex) [(277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 158 = true ∨ valuation q 48 = true := by
  rw [value48, value49, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(272 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (277 : Vertex) [(272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 51 = false := by
  rw [value46, value49, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (261 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 159 = true ∨ valuation q 46 = true ∨ valuation q 51 = true := by
  rw [value46, value50, value51, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(261 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (276 : Vertex) [(261 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 159 = true ∨ valuation q 46 = true ∨ valuation q 49 = true := by
  rw [value46, value49, value50, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(261 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (279 : Vertex) [(261 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 160 = true ∨ valuation q 54 = true := by
  rw [value51, value54, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(287 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (277 : Vertex) [(287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 160 = true ∨ valuation q 50 = true := by
  rw [value50, value51, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(277 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (287 : Vertex) [(277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 161 = true := by
  rw [value52, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (281 : Vertex) (283 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 162 = true ∨ valuation q 52 = true ∨ valuation q 54 = true := by
  rw [value52, value53, value54, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(281 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (267 : Vertex) [(281 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 162 = true ∨ valuation q 47 = true ∨ valuation q 52 = true := by
  rw [value47, value52, value53, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(267 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (287 : Vertex) [(267 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 163 = true ∨ valuation q 53 = true := by
  rw [value53, value54, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(283 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (279 : Vertex) [(283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 163 = true ∨ valuation q 51 = true := by
  rw [value51, value54, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(279 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (283 : Vertex) [(279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 164 = true := by
  rw [value55, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (304 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (288 : Vertex) (304 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 45 = false ∨ valuation q 59 = false ∨ valuation q 77 = false := by
  rw [value45, value56, value59, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (291 : Vertex) (259 : Vertex) (307 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 59 = false ∨ valuation q 61 = false ∨ valuation q 77 = false := by
  rw [value56, value59, value61, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (291 : Vertex) (307 : Vertex) (355 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 48 = false ∨ valuation q 58 = false ∨ valuation q 68 = false := by
  rw [value48, value57, value58, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (272 : Vertex) (305 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 166 = true ∨ valuation q 48 = true ∨ valuation q 55 = true ∨ valuation q 58 = true ∨ valuation q 84 = true := by
  rw [value48, value55, value57, value58, value84, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (304 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(272 : Vertex), (288 : Vertex), (305 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (304 : Vertex) (368 : Vertex) [(272 : Vertex), (288 : Vertex), (305 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 167 = true ∨ valuation q 59 = true := by
  rw [value58, value59, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (304 : Vertex) → w ∈ [(307 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (304 : Vertex) [(307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 168 = true ∨ valuation q 58 = true := by
  rw [value58, value59, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (291 : Vertex) → w ∈ [(305 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (291 : Vertex) [(305 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 168 = true ∨ valuation q 56 = true := by
  rw [value56, value59, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(291 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(291 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 170 = true ∨ valuation q 56 = true ∨ valuation q 65 = true := by
  rw [value56, value61, value65, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (354 : Vertex) → w ∈ [(291 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (354 : Vertex) [(291 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 66 = false ∨ valuation q 69 = false := by
  rw [value62, value63, value66, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (357 : Vertex) (364 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 62 = true ∨ valuation q 70 = true := by
  rw [value62, value63, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ∈ [(356 : Vertex), (373 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (357 : Vertex) [(356 : Vertex), (373 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 172 = true ∨ valuation q 70 = true := by
  rw [value63, value70, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(373 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (356 : Vertex) [(373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 172 = true ∨ valuation q 62 = true := by
  rw [value62, value63, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(356 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (373 : Vertex) [(356 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E201.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112201
