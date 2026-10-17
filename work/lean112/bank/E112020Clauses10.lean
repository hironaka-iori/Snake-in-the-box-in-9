import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 25 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value25, value60, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (113 : Vertex) (243 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 25 = false ∨ valuation q 63 = false ∨ valuation q 67 = false := by
  rw [value25, value60, value63, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (113 : Vertex) (245 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 43 = false ∨ valuation q 51 = false ∨ valuation q 62 = false := by
  rw [value43, value51, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (177 : Vertex) (225 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 43 = false ∨ valuation q 51 = false ∨ valuation q 63 = false := by
  rw [value43, value51, value60, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (177 : Vertex) (225 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 43 = false ∨ valuation q 51 = false ∨ valuation q 67 = false := by
  rw [value43, value51, value60, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (177 : Vertex) (225 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 43 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value43, value60, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (177 : Vertex) (243 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 43 = false ∨ valuation q 62 = false ∨ valuation q 67 = false := by
  rw [value43, value60, value62, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (177 : Vertex) (243 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 43 = false ∨ valuation q 63 = false ∨ valuation q 67 = false := by
  rw [value43, value60, value63, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (177 : Vertex) (245 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 43 = false ∨ valuation q 67 = false ∨ valuation q 114 = false := by
  rw [value43, value60, value67, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (177 : Vertex) (249 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 67 = false := by
  rw [value51, value60, value62, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (225 : Vertex) (243 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 67 = false := by
  rw [value60, value62, value63, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (243 : Vertex) (245 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 43 = true ∨ valuation q 51 = true ∨ valuation q 62 = true ∨ valuation q 63 = true ∨ valuation q 67 = true ∨ valuation q 114 = true := by
  rw [value43, value51, value60, value62, value63, value67, value114, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(177 : Vertex), (225 : Vertex), (243 : Vertex), (245 : Vertex), (249 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (113 : Vertex) [(177 : Vertex), (225 : Vertex), (243 : Vertex), (245 : Vertex), (249 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 25 = true ∨ valuation q 43 = true ∨ valuation q 51 = true ∨ valuation q 62 = true ∨ valuation q 67 = true ∨ valuation q 114 = true := by
  rw [value25, value43, value51, value60, value62, value67, value114, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(113 : Vertex), (177 : Vertex), (225 : Vertex), (243 : Vertex), (249 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (245 : Vertex) [(113 : Vertex), (177 : Vertex), (225 : Vertex), (243 : Vertex), (249 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 26 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value26, value61, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (242 : Vertex) (114 : Vertex) (243 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 26 = false ∨ valuation q 64 = false ∨ valuation q 115 = false := by
  rw [value26, value61, value64, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (242 : Vertex) (114 : Vertex) (246 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 64 = false ∨ valuation q 115 = false := by
  rw [value61, value62, value64, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (242 : Vertex) (243 : Vertex) (246 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 62 = true ∨ valuation q 64 = true ∨ valuation q 115 = true := by
  rw [value61, value62, value64, value115, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(243 : Vertex), (246 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (114 : Vertex) [(243 : Vertex), (246 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 26 = true ∨ valuation q 64 = true ∨ valuation q 115 = true := by
  rw [value26, value61, value64, value115, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(114 : Vertex), (246 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (243 : Vertex) [(114 : Vertex), (246 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 26 = true ∨ valuation q 62 = true ∨ valuation q 115 = true := by
  rw [value26, value61, value62, value115, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(114 : Vertex), (243 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (246 : Vertex) [(114 : Vertex), (243 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 26 = true ∨ valuation q 62 = true ∨ valuation q 64 = true := by
  rw [value26, value61, value62, value64, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(114 : Vertex), (243 : Vertex), (246 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (498 : Vertex) [(114 : Vertex), (243 : Vertex), (246 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 27 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value27, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (241 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 27 = false ∨ valuation q 60 = false ∨ valuation q 65 = false := by
  rw [value27, value60, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (241 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 27 = false ∨ valuation q 60 = false ∨ valuation q 116 = false := by
  rw [value27, value60, value62, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (241 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 27 = false ∨ valuation q 61 = false ∨ valuation q 65 = false := by
  rw [value27, value61, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (242 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 27 = false ∨ valuation q 61 = false ∨ valuation q 68 = false := by
  rw [value27, value61, value62, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (242 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 27 = false ∨ valuation q 61 = false ∨ valuation q 116 = false := by
  rw [value27, value61, value62, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (242 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 27 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value27, value62, value65, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (247 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 27 = false ∨ valuation q 68 = false ∨ valuation q 116 = false := by
  rw [value27, value62, value68, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (115 : Vertex) (251 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 65 = false := by
  rw [value60, value61, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (241 : Vertex) (242 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 68 = false := by
  rw [value60, value61, value62, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (241 : Vertex) (242 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 116 = false := by
  rw [value60, value61, value62, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (241 : Vertex) (242 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 60 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value60, value62, value65, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (241 : Vertex) (247 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E020.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112020
