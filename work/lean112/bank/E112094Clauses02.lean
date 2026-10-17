import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 152 = true ∨ valuation q 47 = true := by
  rw [value47, value48, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(242 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (251 : Vertex) [(242 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 153 = true ∨ valuation q 53 = true := by
  rw [value49, value53, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(252 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (245 : Vertex) [(252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 153 = true ∨ valuation q 50 = true := by
  rw [value49, value50, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(245 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (252 : Vertex) [(245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 40 = false ∨ valuation q 49 = false ∨ valuation q 54 = false := by
  rw [value40, value49, value50, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (229 : Vertex) (244 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 154 = true ∨ valuation q 49 = true ∨ valuation q 54 = true := by
  rw [value49, value50, value54, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(244 : Vertex), (253 : Vertex)] := by decide
  have hg := other_cover q (245 : Vertex) (229 : Vertex) [(244 : Vertex), (253 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 44 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value44, value51, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (233 : Vertex) (251 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 155 = true ∨ valuation q 52 = true ∨ valuation q 54 = true := by
  rw [value51, value52, value54, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(251 : Vertex), (253 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (233 : Vertex) [(251 : Vertex), (253 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 156 = true ∨ valuation q 51 = true := by
  rw [value51, value52, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(249 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (243 : Vertex) [(249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 156 = true ∨ valuation q 48 = true := by
  rw [value48, value52, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(243 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (249 : Vertex) [(243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = true := by
  rw [value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ∈ [(291 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (289 : Vertex) [(291 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 55 = true := by
  rw [value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 160 = true ∨ valuation q 57 = true := by
  rw [value56, value57, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (291 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(307 : Vertex)] := by decide
  have hg := other_cover q (291 : Vertex) (289 : Vertex) [(307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 161 = true ∨ valuation q 66 = true := by
  rw [value57, value66, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (291 : Vertex) → w ∈ [(371 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (291 : Vertex) [(371 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value58, value60, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (354 : Vertex) (358 : Vertex) (362 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 163 = true ∨ valuation q 68 = true := by
  rw [value59, value68, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(373 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (359 : Vertex) [(373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 164 = true ∨ valuation q 58 = true := by
  rw [value58, value60, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (358 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(354 : Vertex)] := by decide
  have hg := other_cover q (358 : Vertex) (359 : Vertex) [(354 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 167 = true ∨ valuation q 69 = true := by
  rw [value63, value69, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(377 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (360 : Vertex) [(377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 58 = false ∨ valuation q 66 = false ∨ valuation q 100 = false := by
  rw [value58, value65, value66, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (370 : Vertex) (354 : Vertex) (371 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 57 = false ∨ valuation q 65 = false ∨ valuation q 70 = false := by
  rw [value57, value65, value66, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (307 : Vertex) (370 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 171 = true ∨ valuation q 71 = true := by
  rw [value67, value71, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(380 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (373 : Vertex) [(380 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 172 = true ∨ valuation q 67 = true := by
  rw [value67, value68, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (357 : Vertex) → w ∈ [(372 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (357 : Vertex) [(372 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 173 = true ∨ valuation q 70 = true := by
  rw [value69, value70, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (377 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(379 : Vertex)] := by decide
  have hg := other_cover q (377 : Vertex) (361 : Vertex) [(379 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 175 = true ∨ valuation q 104 = true := by
  rw [value71, value104, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (380 : Vertex) w → w ∈ region → w ≠ (372 : Vertex) → w ∈ [(508 : Vertex)] := by decide
  have hg := other_cover q (380 : Vertex) (372 : Vertex) [(508 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 176 = true ∨ valuation q 80 = true := by
  rw [value72, value80, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (385 : Vertex) [(400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 177 = true ∨ valuation q 72 = true ∨ valuation q 75 = true := by
  rw [value72, value73, value75, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (387 : Vertex) [(384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 73 = false ∨ valuation q 76 = false ∨ valuation q 82 = false := by
  rw [value73, value74, value76, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (385 : Vertex) (395 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 73 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value73, value75, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (385 : Vertex) (395 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 180 = true ∨ valuation q 75 = true ∨ valuation q 79 = true := by
  rw [value75, value76, value79, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(393 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (387 : Vertex) [(393 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 180 = true ∨ valuation q 74 = true ∨ valuation q 79 = true := by
  rw [value74, value76, value79, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(387 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (393 : Vertex) [(387 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 180 = true ∨ valuation q 74 = true ∨ valuation q 75 = true := by
  rw [value74, value75, value76, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(387 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (399 : Vertex) [(387 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 181 = true ∨ valuation q 79 = true ∨ valuation q 88 = true := by
  rw [value77, value79, value88, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(399 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (393 : Vertex) [(399 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 181 = true ∨ valuation q 75 = true ∨ valuation q 88 = true := by
  rw [value75, value77, value88, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(393 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (399 : Vertex) [(393 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E094.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112094
