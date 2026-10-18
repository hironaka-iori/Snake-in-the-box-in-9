import E112150Semantics
import B112E150Inputs
namespace Snake9.Regrowth.E112150
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 7 = false ∨ valuation q 37 = false ∨ valuation q 40 = false := by
  rw [value7, value37, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (25 : Vertex) (145 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 37 = false ∨ valuation q 40 = false ∨ valuation q 87 = false := by
  rw [value37, value40, value41, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (145 : Vertex) (152 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 150 = true ∨ valuation q 50 = true := by
  rw [value44, value50, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (231 : Vertex) → w ∈ [(235 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (231 : Vertex) [(235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 150 = true ∨ valuation q 47 = true := by
  rw [value44, value47, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(231 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (235 : Vertex) [(231 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 152 = true ∨ valuation q 47 = true := by
  rw [value46, value47, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(231 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (228 : Vertex) [(231 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 51 = false := by
  rw [value44, value46, value47, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (227 : Vertex) (229 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 155 = true ∨ valuation q 50 = true := by
  rw [value49, value50, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(235 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (232 : Vertex) [(235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 44 = false ∨ valuation q 49 = false ∨ valuation q 51 = false := by
  rw [value44, value49, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (234 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value52, value53, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (241 : Vertex) (244 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 159 = true ∨ valuation q 52 = true ∨ valuation q 102 = true := by
  rw [value52, value53, value102, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(240 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (249 : Vertex) [(240 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 164 = true ∨ valuation q 59 = true := by
  rw [value58, value59, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(255 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (246 : Vertex) [(255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 51 = false ∨ valuation q 58 = false ∨ valuation q 106 = false := by
  rw [value51, value58, value59, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (239 : Vertex) (254 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 166 = true ∨ valuation q 61 = true := by
  rw [value60, value61, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (356 : Vertex) w → w ∈ region → w ≠ (372 : Vertex) → w ∈ [(357 : Vertex)] := by decide
  have hg := other_cover q (356 : Vertex) (372 : Vertex) [(357 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 167 = true ∨ valuation q 62 = true := by
  rw [value61, value62, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(359 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (356 : Vertex) [(359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 168 = true ∨ valuation q 66 = true := by
  rw [value62, value66, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (359 : Vertex) w → w ∈ region → w ≠ (357 : Vertex) → w ∈ [(367 : Vertex)] := by decide
  have hg := other_cover q (359 : Vertex) (357 : Vertex) [(367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 169 = true ∨ valuation q 70 = true := by
  rw [value63, value70, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (362 : Vertex) → w ∈ [(376 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (362 : Vertex) [(376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 170 = true ∨ valuation q 63 = true := by
  rw [value63, value64, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(360 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (363 : Vertex) [(360 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 171 = true ∨ valuation q 64 = true := by
  rw [value64, value65, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (363 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(362 : Vertex)] := by decide
  have hg := other_cover q (363 : Vertex) (367 : Vertex) [(362 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 172 = true ∨ valuation q 65 = true ∨ valuation q 73 = true := by
  rw [value65, value66, value73, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(363 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (359 : Vertex) [(363 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 173 = true ∨ valuation q 102 = true := by
  rw [value67, value102, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (369 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(497 : Vertex)] := by decide
  have hg := other_cover q (369 : Vertex) (377 : Vertex) [(497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 174 = true ∨ valuation q 69 = true := by
  rw [value68, value69, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(374 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (356 : Vertex) [(374 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 174 = true ∨ valuation q 60 = true := by
  rw [value60, value68, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (374 : Vertex) → w ∈ [(356 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (374 : Vertex) [(356 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 175 = true ∨ valuation q 68 = true := by
  rw [value68, value69, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (374 : Vertex) w → w ∈ region → w ≠ (382 : Vertex) → w ∈ [(372 : Vertex)] := by decide
  have hg := other_cover q (374 : Vertex) (382 : Vertex) [(372 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 176 = true ∨ valuation q 71 = true := by
  rw [value70, value71, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(377 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (360 : Vertex) [(377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 177 = true ∨ valuation q 67 = true := by
  rw [value67, value71, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (377 : Vertex) w → w ∈ region → w ≠ (376 : Vertex) → w ∈ [(369 : Vertex)] := by decide
  have hg := other_cover q (377 : Vertex) (376 : Vertex) [(369 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 69 = true ∨ valuation q 73 = true := by
  rw [value69, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (382 : Vertex) w → w ∈ region → w ∈ [(374 : Vertex), (383 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (382 : Vertex) [(374 : Vertex), (383 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 69 = false ∨ valuation q 73 = false := by
  rw [value69, value73, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (382 : Vertex) (374 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 72 = true := by
  rw [value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 178 = true := by
  rw [value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change BallClauseLogic.Endpoint q head
  exact (endpoint_iff q head).mpr (Or.inl h.head_fixed.symm)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 82 = false := by
  rw [value74, value75, value77, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 181 = true ∨ valuation q 74 = true ∨ valuation q 78 = true := by
  rw [value74, value75, value78, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(384 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (387 : Vertex) [(384 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 181 = true ∨ valuation q 74 = true ∨ valuation q 76 = true := by
  rw [value74, value75, value76, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(384 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (390 : Vertex) [(384 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E150.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112150
