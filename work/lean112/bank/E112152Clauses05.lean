import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 84 = false := by
  rw [value78, value79, value80, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (419 : Vertex) (421 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 99 = false := by
  rw [value78, value79, value80, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (419 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 99 = false := by
  rw [value78, value80, value84, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (421 : Vertex) (425 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 198 = true ∨ valuation q 80 = true ∨ valuation q 84 = true ∨ valuation q 99 = true := by
  rw [value78, value80, value84, value99, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(421 : Vertex), (425 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (419 : Vertex) [(421 : Vertex), (425 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 199 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 101 = true := by
  rw [value79, value82, value85, value101, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(423 : Vertex), (427 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (417 : Vertex) [(423 : Vertex), (427 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 199 = true ∨ valuation q 78 = true ∨ valuation q 82 = true ∨ valuation q 101 = true := by
  rw [value78, value79, value82, value101, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(417 : Vertex), (423 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (427 : Vertex) [(417 : Vertex), (423 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 199 = true ∨ valuation q 78 = true ∨ valuation q 82 = true ∨ valuation q 85 = true := by
  rw [value78, value79, value82, value85, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(417 : Vertex), (423 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (483 : Vertex) [(417 : Vertex), (423 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 78 = false ∨ valuation q 87 = false ∨ valuation q 102 = false := by
  rw [value78, value80, value87, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (429 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 200 = true ∨ valuation q 82 = true ∨ valuation q 87 = true ∨ valuation q 92 = true ∨ valuation q 102 = true := by
  rw [value80, value82, value87, value92, value102, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(423 : Vertex), (429 : Vertex), (437 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (417 : Vertex) [(423 : Vertex), (429 : Vertex), (437 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 200 = true ∨ valuation q 78 = true ∨ valuation q 87 = true ∨ valuation q 92 = true ∨ valuation q 102 = true := by
  rw [value78, value80, value87, value92, value102, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(417 : Vertex), (429 : Vertex), (437 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (423 : Vertex) [(417 : Vertex), (429 : Vertex), (437 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 200 = true ∨ valuation q 78 = true ∨ valuation q 82 = true ∨ valuation q 87 = true ∨ valuation q 102 = true := by
  rw [value78, value80, value82, value87, value102, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(417 : Vertex), (423 : Vertex), (429 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (437 : Vertex) [(417 : Vertex), (423 : Vertex), (429 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 200 = true ∨ valuation q 78 = true ∨ valuation q 82 = true ∨ valuation q 87 = true ∨ valuation q 92 = true := by
  rw [value78, value80, value82, value87, value92, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(417 : Vertex), (423 : Vertex), (429 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (485 : Vertex) [(417 : Vertex), (423 : Vertex), (429 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 201 = true ∨ valuation q 82 = true ∨ valuation q 93 = true ∨ valuation q 103 = true := by
  rw [value81, value82, value93, value103, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(423 : Vertex), (438 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (166 : Vertex) [(423 : Vertex), (438 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 201 = true ∨ valuation q 28 = true ∨ valuation q 93 = true ∨ valuation q 103 = true := by
  rw [value28, value81, value93, value103, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(166 : Vertex), (438 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (423 : Vertex) [(166 : Vertex), (438 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 201 = true ∨ valuation q 28 = true ∨ valuation q 82 = true ∨ valuation q 103 = true := by
  rw [value28, value81, value82, value103, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (438 : Vertex) → w ∈ [(166 : Vertex), (423 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (438 : Vertex) [(166 : Vertex), (423 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 201 = true ∨ valuation q 28 = true ∨ valuation q 82 = true ∨ valuation q 93 = true := by
  rw [value28, value81, value82, value93, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(166 : Vertex), (423 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (486 : Vertex) [(166 : Vertex), (423 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 29 = false ∨ valuation q 79 = false ∨ valuation q 80 = false := by
  rw [value29, value79, value80, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (419 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 29 = false ∨ valuation q 79 = false ∨ valuation q 81 = false := by
  rw [value29, value79, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (419 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 29 = false ∨ valuation q 79 = false ∨ valuation q 88 = false := by
  rw [value29, value79, value82, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (419 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 29 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value29, value80, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 29 = false ∨ valuation q 81 = false ∨ valuation q 88 = false := by
  rw [value29, value81, value82, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (422 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value79, value80, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (419 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 88 = false := by
  rw [value79, value80, value82, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (419 : Vertex) (421 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 88 = false := by
  rw [value79, value81, value82, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (419 : Vertex) (422 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 88 = false := by
  rw [value80, value81, value82, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (422 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 30 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value30, value83, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (425 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 30 = false ∨ valuation q 84 = false ∨ valuation q 94 = false := by
  rw [value30, value83, value84, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (425 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 30 = false ∨ valuation q 84 = false ∨ valuation q 104 = false := by
  rw [value30, value83, value84, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (425 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 30 = false ∨ valuation q 86 = false ∨ valuation q 94 = false := by
  rw [value30, value83, value86, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 30 = false ∨ valuation q 86 = false ∨ valuation q 104 = false := by
  rw [value30, value83, value86, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (428 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 30 = false ∨ valuation q 94 = false ∨ valuation q 104 = false := by
  rw [value30, value83, value94, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 94 = false := by
  rw [value83, value84, value86, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (425 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E152.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112152
