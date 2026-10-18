import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 80 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value80, value97, value98, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (419 : Vertex) (482 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 80 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value80, value98, value101, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (419 : Vertex) (487 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 80 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value80, value98, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (419 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value97, value98, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (482 : Vertex) (487 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value97, value98, value101, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (482 : Vertex) (487 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 97 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value97, value98, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (482 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 101 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value98, value101, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (487 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 64 = false ∨ valuation q 81 = false ∨ valuation q 96 = false := by
  rw [value64, value81, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (484 : Vertex) (356 : Vertex) (420 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 64 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value64, value81, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (484 : Vertex) (356 : Vertex) (420 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value97, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (482 : Vertex) (484 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 108 = false := by
  rw [value97, value99, value100, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (482 : Vertex) (484 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value97, value99, value100, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (482 : Vertex) (484 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value97, value100, value101, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (482 : Vertex) (487 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 112 = false := by
  rw [value97, value100, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (482 : Vertex) (487 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 97 = false ∨ valuation q 108 = false ∨ valuation q 112 = false := by
  rw [value97, value100, value108, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (482 : Vertex) (494 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 99 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value99, value100, value101, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (484 : Vertex) (487 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 99 = false ∨ valuation q 101 = false ∨ valuation q 112 = false := by
  rw [value99, value100, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (484 : Vertex) (487 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 99 = false ∨ valuation q 108 = false ∨ valuation q 112 = false := by
  rw [value99, value100, value108, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (484 : Vertex) (494 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 108 = false ∨ valuation q 112 = false := by
  rw [value100, value101, value108, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (487 : Vertex) (494 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 218 = true ∨ valuation q 97 = true ∨ valuation q 99 = true ∨ valuation q 101 = true ∨ valuation q 112 = true := by
  rw [value97, value99, value100, value101, value112, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (494 : Vertex) → w ∈ [(482 : Vertex), (484 : Vertex), (487 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (494 : Vertex) [(482 : Vertex), (484 : Vertex), (487 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 33 = false ∨ valuation q 66 = false ∨ valuation q 113 = false := by
  rw [value33, value66, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (231 : Vertex) (359 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 33 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value33, value100, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (231 : Vertex) (486 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 66 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value66, value100, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (359 : Vertex) (486 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 83 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value83, value100, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (423 : Vertex) (486 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 98 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value98, value100, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (483 : Vertex) (486 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 96 = false ∨ valuation q 104 = false ∨ valuation q 114 = false := by
  rw [value96, value102, value104, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (480 : Vertex) (490 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value102, value103, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (489 : Vertex) (490 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 114 = false := by
  rw [value102, value104, value106, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (490 : Vertex) (492 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 220 = true ∨ valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 114 = true := by
  rw [value102, value103, value104, value106, value114, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(489 : Vertex), (490 : Vertex), (492 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (480 : Vertex) [(489 : Vertex), (490 : Vertex), (492 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 220 = true ∨ valuation q 96 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 114 = true := by
  rw [value96, value102, value104, value106, value114, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(480 : Vertex), (490 : Vertex), (492 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (489 : Vertex) [(480 : Vertex), (490 : Vertex), (492 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 220 = true ∨ valuation q 96 = true ∨ valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 106 = true := by
  rw [value96, value102, value103, value104, value106, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(480 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (504 : Vertex) [(480 : Vertex), (489 : Vertex), (490 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 34 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value34, value102, value103, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E104.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112104
