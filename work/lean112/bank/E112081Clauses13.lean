import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 185 = true ∨ valuation q 58 = true ∨ valuation q 63 = true := by
  rw [value58, value63, value68, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(271 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (283 : Vertex) [(271 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 46 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value46, value69, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (256 : Vertex) (321 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 186 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value69, value70, value73, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (256 : Vertex) → w ∈ [(321 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (256 : Vertex) [(321 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 186 = true ∨ valuation q 46 = true ∨ valuation q 73 = true := by
  rw [value46, value69, value73, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(256 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (321 : Vertex) [(256 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 186 = true ∨ valuation q 46 = true ∨ valuation q 70 = true := by
  rw [value46, value69, value70, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(256 : Vertex), (321 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (328 : Vertex) [(256 : Vertex), (321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 47 = false ∨ valuation q 69 = false ∨ valuation q 74 = false := by
  rw [value47, value69, value70, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (257 : Vertex) (320 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 47 = false ∨ valuation q 69 = false ∨ valuation q 78 = false := by
  rw [value47, value69, value70, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (257 : Vertex) (320 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 47 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value47, value70, value74, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (257 : Vertex) (329 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value69, value70, value74, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (320 : Vertex) (329 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 69 = false ∨ valuation q 78 = false := by
  rw [value69, value78, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (321 : Vertex) (320 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 187 = true ∨ valuation q 47 = true ∨ valuation q 74 = true ∨ valuation q 78 = true := by
  rw [value47, value70, value74, value78, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(257 : Vertex), (329 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(257 : Vertex), (329 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 188 = true ∨ valuation q 72 = true ∨ valuation q 82 = true := by
  rw [value71, value72, value82, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(327 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (262 : Vertex) [(327 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 188 = true ∨ valuation q 51 = true ∨ valuation q 82 = true := by
  rw [value51, value71, value82, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(262 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (327 : Vertex) [(262 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 188 = true ∨ valuation q 51 = true ∨ valuation q 72 = true := by
  rw [value51, value71, value72, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(262 : Vertex), (327 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (342 : Vertex) [(262 : Vertex), (327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 52 = false ∨ valuation q 71 = false ∨ valuation q 77 = false := by
  rw [value52, value71, value72, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (263 : Vertex) (326 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 189 = true ∨ valuation q 52 = true ∨ valuation q 77 = true := by
  rw [value52, value72, value77, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(263 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (326 : Vertex) [(263 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 189 = true ∨ valuation q 52 = true ∨ valuation q 71 = true := by
  rw [value52, value71, value72, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(263 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (335 : Vertex) [(263 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 53 = false ∨ valuation q 69 = false ∨ valuation q 74 = false := by
  rw [value53, value69, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (264 : Vertex) (320 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 53 = false ∨ valuation q 69 = false := by
  rw [value53, value69, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (328 : Vertex) (264 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 190 = true ∨ valuation q 53 = true ∨ valuation q 74 = true := by
  rw [value53, value73, value74, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(264 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (320 : Vertex) [(264 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 190 = true ∨ valuation q 53 = true ∨ valuation q 69 = true := by
  rw [value53, value69, value73, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(264 : Vertex), (320 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (329 : Vertex) [(264 : Vertex), (320 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 191 = true ∨ valuation q 73 = true ∨ valuation q 75 = true ∨ valuation q 76 = true := by
  rw [value73, value74, value75, value76, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(328 : Vertex), (331 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (321 : Vertex) [(328 : Vertex), (331 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 191 = true ∨ valuation q 70 = true ∨ valuation q 75 = true ∨ valuation q 76 = true := by
  rw [value70, value74, value75, value76, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(321 : Vertex), (331 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (328 : Vertex) [(321 : Vertex), (331 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 191 = true ∨ valuation q 70 = true ∨ valuation q 73 = true ∨ valuation q 75 = true := by
  rw [value70, value73, value74, value75, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(321 : Vertex), (328 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (333 : Vertex) [(321 : Vertex), (328 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 55 = false ∨ valuation q 74 = false ∨ valuation q 77 = false := by
  rw [value55, value74, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (331 : Vertex) (267 : Vertex) (329 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 192 = true ∨ valuation q 55 = true ∨ valuation q 74 = true := by
  rw [value55, value74, value75, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(267 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (335 : Vertex) [(267 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 85 = false := by
  rw [value74, value76, value77, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (329 : Vertex) (335 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 58 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value58, value72, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (335 : Vertex) (271 : Vertex) (327 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 58 = false ∨ valuation q 72 = false ∨ valuation q 76 = false := by
  rw [value58, value72, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (335 : Vertex) (271 : Vertex) (327 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 194 = true ∨ valuation q 58 = true ∨ valuation q 72 = true ∨ valuation q 76 = true := by
  rw [value58, value72, value76, value77, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (331 : Vertex) → w ∈ [(271 : Vertex), (327 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (331 : Vertex) [(271 : Vertex), (327 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 194 = true ∨ valuation q 58 = true ∨ valuation q 72 = true ∨ valuation q 75 = true := by
  rw [value58, value72, value75, value77, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(271 : Vertex), (327 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (333 : Vertex) [(271 : Vertex), (327 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 59 = false ∨ valuation q 70 = false ∨ valuation q 80 = false := by
  rw [value59, value70, value78, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (337 : Vertex) (273 : Vertex) (321 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E081.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112081
