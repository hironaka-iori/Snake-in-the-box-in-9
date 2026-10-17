import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 185 = true ∨ valuation q 50 = true ∨ valuation q 58 = true := by
  rw [value50, value58, value59, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (191 : Vertex) → w ∈ [(173 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (191 : Vertex) [(173 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 30 = false ∨ valuation q 56 = false ∨ valuation q 58 = false := by
  rw [value30, value56, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (182 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 186 = true ∨ valuation q 30 = true ∨ valuation q 58 = true ∨ valuation q 61 = true := by
  rw [value30, value58, value60, value61, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(62 : Vertex), (188 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (182 : Vertex) [(62 : Vertex), (188 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 186 = true ∨ valuation q 30 = true ∨ valuation q 56 = true ∨ valuation q 61 = true := by
  rw [value30, value56, value60, value61, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(62 : Vertex), (182 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (188 : Vertex) [(62 : Vertex), (182 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 31 = false ∨ valuation q 51 = false ∨ valuation q 59 = false := by
  rw [value31, value51, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (63 : Vertex) (175 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 31 = false ∨ valuation q 51 = false ∨ valuation q 68 = false := by
  rw [value31, value51, value61, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (63 : Vertex) (175 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 31 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value31, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (63 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 31 = false ∨ valuation q 59 = false ∨ valuation q 68 = false := by
  rw [value31, value59, value61, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (63 : Vertex) (189 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 31 = false ∨ valuation q 60 = false ∨ valuation q 68 = false := by
  rw [value31, value60, value61, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (63 : Vertex) (190 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 31 = false ∨ valuation q 68 = false ∨ valuation q 109 = false := by
  rw [value31, value61, value68, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (63 : Vertex) (255 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value51, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 59 = false ∨ valuation q 68 = false := by
  rw [value51, value59, value61, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (189 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 59 = false ∨ valuation q 109 = false := by
  rw [value51, value59, value61, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (189 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 68 = false := by
  rw [value51, value60, value61, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (190 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 109 = false := by
  rw [value51, value60, value61, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (190 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 68 = false ∨ valuation q 109 = false := by
  rw [value51, value61, value68, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (255 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 68 = false := by
  rw [value59, value60, value61, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (189 : Vertex) (190 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 109 = false := by
  rw [value59, value60, value61, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (189 : Vertex) (190 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 59 = false ∨ valuation q 68 = false ∨ valuation q 109 = false := by
  rw [value59, value61, value68, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (189 : Vertex) (255 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 60 = false ∨ valuation q 68 = false ∨ valuation q 109 = false := by
  rw [value60, value61, value68, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (190 : Vertex) (255 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 64 = true := by
  rw [value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ∈ [(247 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (245 : Vertex) [(247 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 63 = true := by
  rw [value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 190 = true ∨ valuation q 68 = true := by
  rw [value64, value68, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (245 : Vertex) [(255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 191 = true ∨ valuation q 66 = true := by
  rw [value65, value66, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(249 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (184 : Vertex) [(249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 191 = true ∨ valuation q 57 = true := by
  rw [value57, value65, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(184 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (249 : Vertex) [(184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 67 = false := by
  rw [value62, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (233 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 192 = true ∨ valuation q 65 = true ∨ valuation q 67 = true := by
  rw [value65, value66, value67, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(248 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (233 : Vertex) [(248 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 192 = true ∨ valuation q 62 = true ∨ valuation q 67 = true := by
  rw [value62, value66, value67, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(233 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (248 : Vertex) [(233 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 192 = true ∨ valuation q 62 = true ∨ valuation q 65 = true := by
  rw [value62, value65, value66, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(233 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (251 : Vertex) [(233 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 193 = true ∨ valuation q 68 = true := by
  rw [value67, value68, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (249 : Vertex) [(255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 193 = true ∨ valuation q 66 = true := by
  rw [value66, value67, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(249 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (255 : Vertex) [(249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 67 = false := by
  rw [value61, value64, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (191 : Vertex) (247 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E121.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112121
