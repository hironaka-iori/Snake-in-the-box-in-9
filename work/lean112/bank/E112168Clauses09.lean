import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 171 = true ∨ valuation q 45 = true ∨ valuation q 56 = true := by
  rw [value45, value56, value57, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(195 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (209 : Vertex) [(195 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 171 = true ∨ valuation q 45 = true ∨ valuation q 55 = true := by
  rw [value45, value55, value57, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(195 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (210 : Vertex) [(195 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 172 = true ∨ valuation q 56 = true ∨ valuation q 109 = true := by
  rw [value56, value58, value109, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(210 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (222 : Vertex) [(210 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 172 = true ∨ valuation q 56 = true ∨ valuation q 64 = true := by
  rw [value56, value58, value64, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(210 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (470 : Vertex) [(210 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 18 = false ∨ valuation q 54 = false ∨ valuation q 60 = false := by
  rw [value18, value54, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (208 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 18 = false ∨ valuation q 54 = false ∨ valuation q 61 = false := by
  rw [value18, value54, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (208 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 18 = false ∨ valuation q 54 = false ∨ valuation q 62 = false := by
  rw [value18, value54, value59, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (208 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 18 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value18, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 18 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value18, value59, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (217 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 18 = false ∨ valuation q 60 = false ∨ valuation q 111 = false := by
  rw [value18, value59, value60, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (217 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 18 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value18, value59, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 54 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value54, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 54 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value54, value59, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (217 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 54 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value54, value59, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value59, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (217 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 111 = false := by
  rw [value59, value60, value61, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (217 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 62 = false ∨ valuation q 111 = false := by
  rw [value59, value60, value62, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (217 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 111 = false := by
  rw [value59, value61, value62, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (218 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 48 = false ∨ valuation q 59 = false := by
  rw [value19, value48, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (89 : Vertex) (201 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 48 = false ∨ valuation q 112 = false := by
  rw [value19, value48, value60, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (89 : Vertex) (201 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 48 = false ∨ valuation q 55 = false ∨ valuation q 59 = false := by
  rw [value48, value55, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (201 : Vertex) (209 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 48 = false ∨ valuation q 55 = false ∨ valuation q 63 = false := by
  rw [value48, value55, value60, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (201 : Vertex) (209 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 48 = false ∨ valuation q 63 = false ∨ valuation q 112 = false := by
  rw [value48, value60, value63, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (201 : Vertex) (221 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 20 = false ∨ valuation q 38 = false ∨ valuation q 64 = false := by
  rw [value20, value38, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (154 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 38 = false ∨ valuation q 49 = false ∨ valuation q 64 = false := by
  rw [value38, value49, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (202 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 38 = false ∨ valuation q 56 = false ∨ valuation q 59 = false := by
  rw [value38, value56, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (210 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 38 = false ∨ valuation q 56 = false ∨ valuation q 64 = false := by
  rw [value38, value56, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (210 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 175 = true ∨ valuation q 20 = true ∨ valuation q 49 = true ∨ valuation q 56 = true ∨ valuation q 59 = true ∨ valuation q 64 = true := by
  rw [value20, value49, value56, value59, value61, value64, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(90 : Vertex), (202 : Vertex), (210 : Vertex), (216 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (154 : Vertex) [(90 : Vertex), (202 : Vertex), (210 : Vertex), (216 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 175 = true ∨ valuation q 20 = true ∨ valuation q 38 = true ∨ valuation q 49 = true ∨ valuation q 59 = true ∨ valuation q 64 = true := by
  rw [value20, value38, value49, value59, value61, value64, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(90 : Vertex), (154 : Vertex), (202 : Vertex), (216 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (210 : Vertex) [(90 : Vertex), (154 : Vertex), (202 : Vertex), (216 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 175 = true ∨ valuation q 20 = true ∨ valuation q 38 = true ∨ valuation q 49 = true ∨ valuation q 56 = true ∨ valuation q 59 = true := by
  rw [value20, value38, value49, value56, value59, value61, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(90 : Vertex), (154 : Vertex), (202 : Vertex), (210 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (222 : Vertex) [(90 : Vertex), (154 : Vertex), (202 : Vertex), (210 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 176 = true ∨ valuation q 59 = true ∨ valuation q 63 = true ∨ valuation q 64 = true := by
  rw [value59, value62, value63, value64, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(216 : Vertex), (221 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (204 : Vertex) [(216 : Vertex), (221 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 176 = true ∨ valuation q 50 = true ∨ valuation q 63 = true ∨ valuation q 64 = true := by
  rw [value50, value62, value63, value64, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(204 : Vertex), (221 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (216 : Vertex) [(204 : Vertex), (221 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block9 (q : Snake 81) (h : Conditions q) : B112E168.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112168
