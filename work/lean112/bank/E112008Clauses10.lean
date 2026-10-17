import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 46 = false ∨ valuation q 69 = false ∨ valuation q 108 = false := by
  rw [value46, value51, value69, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (183 : Vertex) (255 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 69 = false := by
  rw [value49, value50, value51, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (187 : Vertex) (189 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 69 = false ∨ valuation q 108 = false := by
  rw [value49, value51, value69, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (187 : Vertex) (255 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 69 = false ∨ valuation q 108 = false := by
  rw [value50, value51, value69, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (189 : Vertex) (255 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 19 = false ∨ valuation q 34 = false ∨ valuation q 53 = false := by
  rw [value19, value34, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (162 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 19 = false ∨ valuation q 34 = false ∨ valuation q 57 = false := by
  rw [value19, value34, value52, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (162 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 19 = false ∨ valuation q 34 = false ∨ valuation q 63 = false := by
  rw [value19, value34, value52, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (162 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 19 = false ∨ valuation q 53 = false ∨ valuation q 57 = false := by
  rw [value19, value52, value53, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 19 = false ∨ valuation q 53 = false ∨ valuation q 63 = false := by
  rw [value19, value52, value53, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (227 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 19 = false ∨ valuation q 57 = false ∨ valuation q 63 = false := by
  rw [value19, value52, value57, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (234 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 34 = false ∨ valuation q 53 = false ∨ valuation q 57 = false := by
  rw [value34, value52, value53, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 34 = false ∨ valuation q 53 = false ∨ valuation q 63 = false := by
  rw [value34, value52, value53, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (227 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 34 = false ∨ valuation q 57 = false ∨ valuation q 63 = false := by
  rw [value34, value52, value57, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (234 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 57 = false ∨ valuation q 63 = false := by
  rw [value52, value53, value57, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (227 : Vertex) (234 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 176 = true ∨ valuation q 19 = true ∨ valuation q 34 = true ∨ valuation q 57 = true ∨ valuation q 63 = true := by
  rw [value19, value34, value52, value57, value63, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (226 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(98 : Vertex), (162 : Vertex), (234 : Vertex), (242 : Vertex)] := by decide
  have hg := other_cover q (226 : Vertex) (227 : Vertex) [(98 : Vertex), (162 : Vertex), (234 : Vertex), (242 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 64 = false := by
  rw [value52, value53, value55, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (226 : Vertex) (231 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 177 = true ∨ valuation q 55 = true ∨ valuation q 58 = true ∨ valuation q 64 = true := by
  rw [value53, value55, value58, value64, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(231 : Vertex), (235 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (226 : Vertex) [(231 : Vertex), (235 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 177 = true ∨ valuation q 52 = true ∨ valuation q 55 = true ∨ valuation q 58 = true := by
  rw [value52, value53, value55, value58, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(226 : Vertex), (231 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (243 : Vertex) [(226 : Vertex), (231 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 36 = false ∨ valuation q 55 = false ∨ valuation q 59 = false := by
  rw [value36, value54, value55, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (165 : Vertex) (231 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 178 = true ∨ valuation q 55 = true ∨ valuation q 59 = true := by
  rw [value54, value55, value59, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(231 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (165 : Vertex) [(231 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 178 = true ∨ valuation q 36 = true ∨ valuation q 59 = true := by
  rw [value36, value54, value59, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (231 : Vertex) → w ∈ [(165 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (231 : Vertex) [(165 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 178 = true ∨ valuation q 36 = true ∨ valuation q 55 = true := by
  rw [value36, value54, value55, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(165 : Vertex), (231 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (237 : Vertex) [(165 : Vertex), (231 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 20 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value20, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (227 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 20 = false ∨ valuation q 53 = false ∨ valuation q 60 = false := by
  rw [value20, value53, value55, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (227 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 20 = false ∨ valuation q 54 = false ∨ valuation q 112 = false := by
  rw [value20, value54, value55, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (103 : Vertex) (229 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 60 = false := by
  rw [value53, value54, value55, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (227 : Vertex) (229 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 112 = false := by
  rw [value53, value54, value55, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (227 : Vertex) (229 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 53 = false ∨ valuation q 60 = false ∨ valuation q 112 = false := by
  rw [value53, value55, value60, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (227 : Vertex) (239 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 54 = false ∨ valuation q 60 = false ∨ valuation q 112 = false := by
  rw [value54, value55, value60, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (229 : Vertex) (239 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 22 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value22, value56, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (105 : Vertex) (235 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 180 = true ∨ valuation q 58 = true ∨ valuation q 59 = true ∨ valuation q 114 = true := by
  rw [value56, value58, value59, value114, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(235 : Vertex), (237 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (105 : Vertex) [(235 : Vertex), (237 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 180 = true ∨ valuation q 22 = true ∨ valuation q 58 = true ∨ valuation q 114 = true := by
  rw [value22, value56, value58, value114, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(105 : Vertex), (235 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (237 : Vertex) [(105 : Vertex), (235 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E008.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112008
