import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 192 = true ∨ valuation q 27 = true ∨ valuation q 59 = true := by
  rw [value27, value59, value65, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(110 : Vertex), (230 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (236 : Vertex) [(110 : Vertex), (230 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 67 = false := by
  rw [value49, value56, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (242 : Vertex) (210 : Vertex) (226 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 69 = false := by
  rw [value49, value56, value66, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (242 : Vertex) (210 : Vertex) (226 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 49 = false ∨ valuation q 67 = false ∨ valuation q 69 = false := by
  rw [value49, value66, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (242 : Vertex) (210 : Vertex) (243 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 56 = false ∨ valuation q 67 = false ∨ valuation q 69 = false := by
  rw [value56, value66, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (242 : Vertex) (226 : Vertex) (243 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 193 = true ∨ valuation q 49 = true ∨ valuation q 56 = true ∨ valuation q 69 = true := by
  rw [value49, value56, value66, value69, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(210 : Vertex), (226 : Vertex), (246 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (243 : Vertex) [(210 : Vertex), (226 : Vertex), (246 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 193 = true ∨ valuation q 49 = true ∨ valuation q 56 = true ∨ valuation q 67 = true := by
  rw [value49, value56, value66, value67, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(210 : Vertex), (226 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (246 : Vertex) [(210 : Vertex), (226 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 29 = false ∨ valuation q 57 = false ∨ valuation q 71 = false := by
  rw [value29, value57, value67, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (227 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 29 = false ∨ valuation q 66 = false ∨ valuation q 71 = false := by
  rw [value29, value66, value67, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (242 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 194 = true ∨ valuation q 57 = true ∨ valuation q 66 = true ∨ valuation q 71 = true := by
  rw [value57, value66, value67, value71, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (115 : Vertex) → w ∈ [(227 : Vertex), (242 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (115 : Vertex) [(227 : Vertex), (242 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 194 = true ∨ valuation q 29 = true ∨ valuation q 66 = true ∨ valuation q 71 = true := by
  rw [value29, value66, value67, value71, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(115 : Vertex), (242 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (227 : Vertex) [(115 : Vertex), (242 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 194 = true ∨ valuation q 29 = true ∨ valuation q 57 = true ∨ valuation q 71 = true := by
  rw [value29, value57, value67, value71, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (242 : Vertex) → w ∈ [(115 : Vertex), (227 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (242 : Vertex) [(115 : Vertex), (227 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 194 = true ∨ valuation q 29 = true ∨ valuation q 57 = true ∨ valuation q 66 = true := by
  rw [value29, value57, value66, value67, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(115 : Vertex), (227 : Vertex), (242 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (251 : Vertex) [(115 : Vertex), (227 : Vertex), (242 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 58 = true := by
  rw [value58, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ∈ [(229 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (245 : Vertex) [(229 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 195 = true := by
  rw [value68, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (245 : Vertex) (229 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 69 = true := by
  rw [value69, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (246 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 31 = true ∨ valuation q 59 = true ∨ valuation q 66 = true := by
  rw [value31, value59, value66, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (246 : Vertex) w → w ∈ region → w ∈ [(118 : Vertex), (230 : Vertex), (242 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (246 : Vertex) [(118 : Vertex), (230 : Vertex), (242 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 31 = false ∨ valuation q 59 = false ∨ valuation q 66 = false := by
  rw [value31, value59, value66, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (118 : Vertex) (230 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 196 = true ∨ valuation q 59 = true ∨ valuation q 66 = true := by
  rw [value59, value66, value69, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (246 : Vertex) w → w ∈ region → w ≠ (118 : Vertex) → w ∈ [(230 : Vertex), (242 : Vertex)] := by decide
  have hg := other_cover q (246 : Vertex) (118 : Vertex) [(230 : Vertex), (242 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 196 = true ∨ valuation q 31 = true ∨ valuation q 66 = true := by
  rw [value31, value66, value69, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (246 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [(118 : Vertex), (242 : Vertex)] := by decide
  have hg := other_cover q (246 : Vertex) (230 : Vertex) [(118 : Vertex), (242 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 196 = true ∨ valuation q 31 = true ∨ valuation q 59 = true := by
  rw [value31, value59, value69, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (246 : Vertex) w → w ∈ region → w ≠ (242 : Vertex) → w ∈ [(118 : Vertex), (230 : Vertex)] := by decide
  have hg := other_cover q (246 : Vertex) (242 : Vertex) [(118 : Vertex), (230 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 32 = false ∨ valuation q 60 = false ∨ valuation q 72 = false := by
  rw [value32, value60, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (120 : Vertex) (232 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 197 = true ∨ valuation q 60 = true ∨ valuation q 72 = true := by
  rw [value60, value70, value72, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(232 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (120 : Vertex) [(232 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 197 = true ∨ valuation q 32 = true ∨ valuation q 60 = true := by
  rw [value32, value60, value70, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(120 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (252 : Vertex) [(120 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 62 = false ∨ valuation q 67 = false ∨ valuation q 73 = false := by
  rw [value62, value67, value71, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (243 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 198 = true ∨ valuation q 62 = true ∨ valuation q 73 = true := by
  rw [value62, value71, value73, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(235 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (243 : Vertex) [(235 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 198 = true ∨ valuation q 62 = true ∨ valuation q 67 = true := by
  rw [value62, value67, value71, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(235 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (255 : Vertex) [(235 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 72 = true := by
  rw [value72, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (252 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 54 = true ∨ valuation q 63 = true ∨ valuation q 70 = true := by
  rw [value54, value63, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (252 : Vertex) w → w ∈ region → w ∈ [(220 : Vertex), (236 : Vertex), (248 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (252 : Vertex) [(220 : Vertex), (236 : Vertex), (248 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 54 = false ∨ valuation q 63 = false ∨ valuation q 70 = false := by
  rw [value54, value63, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (252 : Vertex) (220 : Vertex) (236 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 54 = false ∨ valuation q 70 = false := by
  rw [value54, value70, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (252 : Vertex) (220 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 199 = true ∨ valuation q 63 = true ∨ valuation q 70 = true := by
  rw [value63, value70, value72, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (252 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(236 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (252 : Vertex) (220 : Vertex) [(236 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block15 (q : Snake 81) (h : Conditions q) : B112E260.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112260
