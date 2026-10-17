import E112225Semantics
import B112E225Inputs
namespace Snake9.Regrowth.E112225
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 147 = true ∨ valuation q 38 = true := by
  rw [value38, value43, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(225 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (232 : Vertex) [(225 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 148 = true ∨ valuation q 45 = true := by
  rw [value44, value45, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [(239 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (230 : Vertex) [(239 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 148 = true ∨ valuation q 40 = true := by
  rw [value40, value44, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (239 : Vertex) → w ∈ [(230 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (239 : Vertex) [(230 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 149 = true ∨ valuation q 41 = true ∨ valuation q 53 = true := by
  rw [value41, value45, value53, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(231 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (239 : Vertex) (238 : Vertex) [(231 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 149 = true ∨ valuation q 41 = true ∨ valuation q 44 = true := by
  rw [value41, value44, value45, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(231 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (239 : Vertex) (255 : Vertex) [(231 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value46, value47, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (242 : Vertex) (244 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 151 = true ∨ valuation q 48 = true := by
  rw [value47, value48, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(243 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (240 : Vertex) [(243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 151 = true ∨ valuation q 46 = true := by
  rw [value46, value47, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(240 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (243 : Vertex) [(240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 46 = true ∨ valuation q 51 = true := by
  rw [value46, value49, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ∈ [(240 : Vertex), (252 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (244 : Vertex) [(240 : Vertex), (252 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 153 = true ∨ valuation q 46 = true := by
  rw [value46, value49, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(240 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (252 : Vertex) [(240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 52 = false := by
  rw [value49, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (252 : Vertex) (244 : Vertex) (248 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 156 = true ∨ valuation q 53 = true := by
  rw [value52, value53, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (253 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(255 : Vertex)] := by decide
  have hg := other_cover q (253 : Vertex) (252 : Vertex) [(255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 157 = true ∨ valuation q 52 = true := by
  rw [value52, value53, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (239 : Vertex) → w ∈ [(253 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (239 : Vertex) [(253 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 157 = true ∨ valuation q 45 = true := by
  rw [value45, value53, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (253 : Vertex) → w ∈ [(239 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (253 : Vertex) [(239 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 158 = true ∨ valuation q 61 = true := by
  rw [value54, value61, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (297 : Vertex) w → w ∈ region → w ≠ (313 : Vertex) → w ∈ [(361 : Vertex)] := by decide
  have hg := other_cover q (297 : Vertex) (313 : Vertex) [(361 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 159 = true ∨ valuation q 54 = true := by
  rw [value54, value55, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (313 : Vertex) w → w ∈ region → w ≠ (315 : Vertex) → w ∈ [(297 : Vertex)] := by decide
  have hg := other_cover q (313 : Vertex) (315 : Vertex) [(297 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 55 = true := by
  rw [value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (315 : Vertex) w → w ∈ region → w ∈ [(313 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (315 : Vertex) [(313 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 56 = true := by
  rw [value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 163 = true ∨ valuation q 102 = true := by
  rw [value59, value102, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (358 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(486 : Vertex)] := by decide
  have hg := other_cover q (358 : Vertex) (366 : Vertex) [(486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 68 = false ∨ valuation q 103 = false := by
  rw [value60, value61, value68, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (361 : Vertex) (376 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 64 = false := by
  rw [value58, value61, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (361 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 167 = true ∨ valuation q 59 = true := by
  rw [value59, value63, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(358 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (367 : Vertex) [(358 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 168 = true ∨ valuation q 62 = true ∨ valuation q 63 = true := by
  rw [value62, value63, value64, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(363 : Vertex), (366 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (383 : Vertex) [(363 : Vertex), (366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 169 = true ∨ valuation q 66 = true := by
  rw [value65, value66, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ≠ (376 : Vertex) → w ∈ [(370 : Vertex)] := by decide
  have hg := other_cover q (368 : Vertex) (376 : Vertex) [(370 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 170 = true ∨ valuation q 67 = true := by
  rw [value66, value67, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (370 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(371 : Vertex)] := by decide
  have hg := other_cover q (370 : Vertex) (368 : Vertex) [(371 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 171 = true ∨ valuation q 58 = true := by
  rw [value58, value67, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (371 : Vertex) w → w ∈ region → w ≠ (370 : Vertex) → w ∈ [(355 : Vertex)] := by decide
  have hg := other_cover q (371 : Vertex) (370 : Vertex) [(355 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 172 = true ∨ valuation q 60 = true ∨ valuation q 65 = true := by
  rw [value60, value65, value68, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (380 : Vertex) → w ∈ [(360 : Vertex), (368 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (380 : Vertex) [(360 : Vertex), (368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 174 = true ∨ valuation q 71 = true := by
  rw [value70, value71, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (380 : Vertex) → w ∈ [(383 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (380 : Vertex) [(383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 175 = true ∨ valuation q 64 = true := by
  rw [value64, value71, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ≠ (381 : Vertex) → w ∈ [(367 : Vertex)] := by decide
  have hg := other_cover q (383 : Vertex) (381 : Vertex) [(367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 77 = false := by
  rw [value72, value73, value74, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 72 = true ∨ valuation q 75 = true ∨ valuation q 79 = true := by
  rw [value72, value73, value75, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ∈ [(384 : Vertex), (390 : Vertex), (394 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (386 : Vertex) [(384 : Vertex), (390 : Vertex), (394 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 177 = true ∨ valuation q 75 = true ∨ valuation q 79 = true := by
  rw [value73, value75, value79, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(390 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (384 : Vertex) [(390 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E225.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112225
