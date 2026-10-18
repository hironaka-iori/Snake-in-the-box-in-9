import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 50 = false ∨ valuation q 88 = false ∨ valuation q 101 = false := by
  rw [value50, value81, value88, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (394 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 88 = false := by
  rw [value80, value81, value82, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (384 : Vertex) (387 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 84 = false ∨ valuation q 88 = false := by
  rw [value81, value82, value84, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (387 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 199 = true ∨ valuation q 50 = true ∨ valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 88 = true ∨ valuation q 101 = true := by
  rw [value50, value80, value81, value82, value84, value88, value101, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(258 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (394 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (130 : Vertex) [(258 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (394 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 199 = true ∨ valuation q 16 = true ∨ valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 88 = true ∨ valuation q 101 = true := by
  rw [value16, value80, value81, value82, value84, value88, value101, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(130 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (394 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (258 : Vertex) [(130 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (394 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 199 = true ∨ valuation q 16 = true ∨ valuation q 50 = true ∨ valuation q 80 = true ∨ valuation q 84 = true ∨ valuation q 88 = true ∨ valuation q 101 = true := by
  rw [value16, value50, value80, value81, value84, value88, value101, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(130 : Vertex), (258 : Vertex), (384 : Vertex), (390 : Vertex), (394 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (387 : Vertex) [(130 : Vertex), (258 : Vertex), (384 : Vertex), (390 : Vertex), (394 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 199 = true ∨ valuation q 16 = true ∨ valuation q 50 = true ∨ valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 88 = true ∨ valuation q 101 = true := by
  rw [value16, value50, value80, value81, value82, value88, value101, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(130 : Vertex), (258 : Vertex), (384 : Vertex), (387 : Vertex), (394 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (390 : Vertex) [(130 : Vertex), (258 : Vertex), (384 : Vertex), (387 : Vertex), (394 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 199 = true ∨ valuation q 16 = true ∨ valuation q 50 = true ∨ valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 101 = true := by
  rw [value16, value50, value80, value81, value82, value84, value101, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(130 : Vertex), (258 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (394 : Vertex) [(130 : Vertex), (258 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 17 = false ∨ valuation q 51 = false ∨ valuation q 81 = false := by
  rw [value17, value51, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 17 = false ∨ valuation q 51 = false ∨ valuation q 85 = false := by
  rw [value17, value51, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 17 = false ∨ valuation q 51 = false ∨ valuation q 92 = false := by
  rw [value17, value51, value82, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 17 = false ∨ valuation q 51 = false ∨ valuation q 102 = false := by
  rw [value17, value51, value82, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 17 = false ∨ valuation q 81 = false ∨ valuation q 85 = false := by
  rw [value17, value81, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (386 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 17 = false ∨ valuation q 81 = false ∨ valuation q 92 = false := by
  rw [value17, value81, value82, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (386 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 17 = false ∨ valuation q 85 = false ∨ valuation q 92 = false := by
  rw [value17, value82, value85, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 17 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value17, value82, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 51 = false ∨ valuation q 81 = false ∨ valuation q 85 = false := by
  rw [value51, value81, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 51 = false ∨ valuation q 81 = false ∨ valuation q 92 = false := by
  rw [value51, value81, value82, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 51 = false ∨ valuation q 81 = false ∨ valuation q 102 = false := by
  rw [value51, value81, value82, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 51 = false ∨ valuation q 85 = false ∨ valuation q 92 = false := by
  rw [value51, value82, value85, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 51 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value51, value82, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 51 = false ∨ valuation q 92 = false ∨ valuation q 102 = false := by
  rw [value51, value82, value92, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 92 = false := by
  rw [value81, value82, value85, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value81, value82, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 81 = false ∨ valuation q 92 = false ∨ valuation q 102 = false := by
  rw [value81, value82, value92, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 92 = false ∨ valuation q 102 = false := by
  rw [value82, value85, value92, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (391 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 201 = true ∨ valuation q 18 = true ∨ valuation q 80 = true ∨ valuation q 84 = true ∨ valuation q 89 = true := by
  rw [value18, value80, value83, value84, value89, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(132 : Vertex), (384 : Vertex), (390 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (452 : Vertex) [(132 : Vertex), (384 : Vertex), (390 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 85 = false := by
  rw [value81, value83, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 90 = false := by
  rw [value81, value83, value84, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 94 = false := by
  rw [value81, value83, value84, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 90 = false := by
  rw [value81, value84, value85, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (391 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 94 = false := by
  rw [value81, value84, value85, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (391 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E007.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112007
