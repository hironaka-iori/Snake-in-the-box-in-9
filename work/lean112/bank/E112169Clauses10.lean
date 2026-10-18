import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 14 = false ∨ valuation q 62 = false ∨ valuation q 82 = false := by
  rw [value14, value62, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (163 : Vertex) (291 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 199 = true ∨ valuation q 14 = true ∨ valuation q 82 = true ∨ valuation q 87 = true := by
  rw [value14, value82, value83, value87, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (291 : Vertex) → w ∈ [(163 : Vertex), (418 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (291 : Vertex) [(163 : Vertex), (418 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value84, value85, value88, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 200 = true ∨ valuation q 88 = true ∨ valuation q 91 = true := by
  rw [value84, value88, value91, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(428 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (421 : Vertex) [(428 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 200 = true ∨ valuation q 85 = true ∨ valuation q 91 = true := by
  rw [value84, value85, value91, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(421 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (428 : Vertex) [(421 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 84 = false ∨ valuation q 92 = false := by
  rw [value15, value84, value85, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (420 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 201 = true ∨ valuation q 84 = true ∨ valuation q 92 = true := by
  rw [value84, value85, value92, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(420 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (165 : Vertex) [(420 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 201 = true ∨ valuation q 15 = true ∨ valuation q 92 = true := by
  rw [value15, value85, value92, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(165 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (420 : Vertex) [(165 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 201 = true ∨ valuation q 15 = true ∨ valuation q 84 = true := by
  rw [value15, value84, value85, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(165 : Vertex), (420 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (437 : Vertex) [(165 : Vertex), (420 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 82 = false ∨ valuation q 89 = false ∨ valuation q 96 = false := by
  rw [value82, value86, value89, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (418 : Vertex) (430 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 96 = false := by
  rw [value86, value87, value89, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (427 : Vertex) (430 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 202 = true ∨ valuation q 87 = true ∨ valuation q 89 = true ∨ valuation q 96 = true := by
  rw [value86, value87, value89, value96, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (418 : Vertex) → w ∈ [(427 : Vertex), (430 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (418 : Vertex) [(427 : Vertex), (430 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 202 = true ∨ valuation q 82 = true ∨ valuation q 87 = true ∨ valuation q 96 = true := by
  rw [value82, value86, value87, value96, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(418 : Vertex), (427 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (430 : Vertex) [(418 : Vertex), (427 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 18 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value18, value83, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (419 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 18 = false ∨ valuation q 86 = false ∨ valuation q 97 = false := by
  rw [value18, value86, value87, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 18 = false ∨ valuation q 86 = false ∨ valuation q 105 = false := by
  rw [value18, value86, value87, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (426 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 18 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value18, value87, value97, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (443 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 97 = false := by
  rw [value83, value86, value87, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (419 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 105 = false := by
  rw [value83, value86, value87, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (419 : Vertex) (426 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 88 = true := by
  rw [value88, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (428 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 204 = true ∨ valuation q 89 = true := by
  rw [value88, value89, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(430 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (420 : Vertex) [(430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 204 = true ∨ valuation q 84 = true := by
  rw [value84, value88, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(420 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (430 : Vertex) [(420 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 205 = true ∨ valuation q 88 = true := by
  rw [value88, value89, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(428 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (426 : Vertex) [(428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 205 = true ∨ valuation q 86 = true := by
  rw [value86, value89, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(426 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (428 : Vertex) [(426 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 21 = false ∨ valuation q 63 = false ∨ valuation q 94 = false := by
  rw [value21, value63, value90, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (176 : Vertex) (304 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 21 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value21, value90, value91, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (176 : Vertex) (436 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 63 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value63, value90, value91, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (304 : Vertex) (436 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 84 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value84, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (420 : Vertex) (432 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 84 = false ∨ valuation q 92 = false ∨ valuation q 111 = false := by
  rw [value84, value91, value92, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (420 : Vertex) (437 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 207 = true ∨ valuation q 84 = true ∨ valuation q 90 = true ∨ valuation q 111 = true := by
  rw [value84, value90, value91, value111, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(420 : Vertex), (432 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (437 : Vertex) [(420 : Vertex), (432 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 85 = false ∨ valuation q 91 = false ∨ valuation q 93 = false := by
  rw [value85, value91, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (436 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 208 = true ∨ valuation q 85 = true ∨ valuation q 91 = true := by
  rw [value85, value91, value92, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(421 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (439 : Vertex) [(421 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E169.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112169
