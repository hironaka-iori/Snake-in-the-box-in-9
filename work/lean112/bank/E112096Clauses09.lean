import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 97 = true ∨ valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 110 = true := by
  rw [value97, value99, value101, value103, value110, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(449 : Vertex), (455 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (450 : Vertex) [(449 : Vertex), (455 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 103 = true ∨ valuation q 110 = true := by
  rw [value97, value98, value99, value103, value110, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(449 : Vertex), (450 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (455 : Vertex) [(449 : Vertex), (450 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 110 = true := by
  rw [value97, value98, value99, value101, value110, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(449 : Vertex), (450 : Vertex), (455 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (459 : Vertex) [(449 : Vertex), (450 : Vertex), (455 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 103 = true := by
  rw [value97, value98, value99, value101, value103, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(449 : Vertex), (450 : Vertex), (455 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (467 : Vertex) [(449 : Vertex), (450 : Vertex), (455 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 35 = false ∨ valuation q 61 = false ∨ valuation q 96 = false := by
  rw [value35, value61, value96, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (196 : Vertex) (324 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 35 = false ∨ valuation q 61 = false ∨ valuation q 111 = false := by
  rw [value35, value61, value100, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (196 : Vertex) (324 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 35 = false ∨ valuation q 78 = false ∨ valuation q 96 = false := by
  rw [value35, value78, value96, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (196 : Vertex) (388 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 35 = false ∨ valuation q 78 = false ∨ valuation q 111 = false := by
  rw [value35, value78, value100, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (196 : Vertex) (388 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 35 = false ∨ valuation q 96 = false ∨ valuation q 104 = false := by
  rw [value35, value96, value100, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (196 : Vertex) (448 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 35 = false ∨ valuation q 96 = false ∨ valuation q 111 = false := by
  rw [value35, value96, value100, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (196 : Vertex) (448 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 61 = false ∨ valuation q 78 = false ∨ valuation q 111 = false := by
  rw [value61, value78, value100, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (324 : Vertex) (388 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 61 = false ∨ valuation q 104 = false ∨ valuation q 111 = false := by
  rw [value61, value100, value104, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (324 : Vertex) (460 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 96 = false ∨ valuation q 104 = false := by
  rw [value78, value96, value100, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (388 : Vertex) (448 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 96 = false ∨ valuation q 111 = false := by
  rw [value78, value96, value100, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (388 : Vertex) (448 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 78 = false ∨ valuation q 104 = false ∨ valuation q 111 = false := by
  rw [value78, value100, value104, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (388 : Vertex) (460 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 96 = false ∨ valuation q 104 = false ∨ valuation q 111 = false := by
  rw [value96, value100, value104, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (448 : Vertex) (460 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = false ∨ valuation q 62 = false ∨ valuation q 80 = false := by
  rw [value37, value62, value80, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = false ∨ valuation q 62 = false ∨ valuation q 99 = false := by
  rw [value37, value62, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = false ∨ valuation q 62 = false ∨ valuation q 107 = false := by
  rw [value37, value62, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = false ∨ valuation q 62 = false ∨ valuation q 113 = false := by
  rw [value37, value62, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (327 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = false ∨ valuation q 80 = false ∨ valuation q 99 = false := by
  rw [value37, value80, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = false ∨ valuation q 80 = false ∨ valuation q 107 = false := by
  rw [value37, value80, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = false ∨ valuation q 80 = false ∨ valuation q 113 = false := by
  rw [value37, value80, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value37, value99, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = false ∨ valuation q 99 = false ∨ valuation q 113 = false := by
  rw [value37, value99, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value37, value101, value107, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (463 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 80 = false ∨ valuation q 99 = false := by
  rw [value62, value80, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 80 = false ∨ valuation q 107 = false := by
  rw [value62, value80, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (391 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 80 = false ∨ valuation q 113 = false := by
  rw [value62, value80, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (391 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value62, value99, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 99 = false ∨ valuation q 113 = false := by
  rw [value62, value99, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (451 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value62, value101, value107, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (463 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E096.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112096
