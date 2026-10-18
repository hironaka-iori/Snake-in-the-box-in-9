import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 79 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value79, value82, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (331 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 192 = true ∨ valuation q 83 = true ∨ valuation q 84 = true := by
  rw [value82, value83, value84, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(331 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (321 : Vertex) [(331 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 192 = true ∨ valuation q 79 = true ∨ valuation q 83 = true := by
  rw [value79, value82, value83, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(321 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (333 : Vertex) [(321 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 25 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value25, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (331 : Vertex) (75 : Vertex) (329 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 70 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value70, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (331 : Vertex) (267 : Vertex) (329 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 100 = false := by
  rw [value82, value83, value85, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (331 : Vertex) (329 : Vertex) (335 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 93 = true := by
  rw [value82, value84, value85, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ∈ [(329 : Vertex), (335 : Vertex), (349 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (333 : Vertex) [(329 : Vertex), (335 : Vertex), (349 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 93 = false := by
  rw [value82, value84, value85, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (329 : Vertex) (335 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 194 = true ∨ valuation q 85 = true ∨ valuation q 93 = true := by
  rw [value84, value85, value93, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(335 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (329 : Vertex) [(335 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 194 = true ∨ valuation q 82 = true ∨ valuation q 93 = true := by
  rw [value82, value84, value93, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(329 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (335 : Vertex) [(329 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 194 = true ∨ valuation q 82 = true ∨ valuation q 85 = true := by
  rw [value82, value84, value85, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(329 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (349 : Vertex) [(329 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value81, value83, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (335 : Vertex) (327 : Vertex) (331 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 195 = true ∨ valuation q 83 = true ∨ valuation q 84 = true := by
  rw [value83, value84, value85, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(331 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (327 : Vertex) [(331 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 195 = true ∨ valuation q 81 = true ∨ valuation q 83 = true := by
  rw [value81, value83, value85, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(327 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (333 : Vertex) [(327 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 196 = true ∨ valuation q 88 = true := by
  rw [value86, value88, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(339 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (321 : Vertex) [(339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 196 = true ∨ valuation q 79 = true := by
  rw [value79, value86, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(321 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (339 : Vertex) [(321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value87, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (339 : Vertex) (342 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 197 = true ∨ valuation q 90 = true ∨ valuation q 91 = true := by
  rw [value87, value90, value91, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (338 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(342 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (338 : Vertex) (339 : Vertex) [(342 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 88 = true := by
  rw [value88, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (339 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = true ∨ valuation q 87 = true := by
  rw [value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ∈ [(337 : Vertex), (338 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (339 : Vertex) [(337 : Vertex), (338 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 198 = true ∨ valuation q 87 = true := by
  rw [value87, value88, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(338 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (337 : Vertex) [(338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 198 = true ∨ valuation q 86 = true := by
  rw [value86, value88, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(337 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (338 : Vertex) [(337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 29 = false ∨ valuation q 71 = false ∨ valuation q 90 = false := by
  rw [value29, value71, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (84 : Vertex) (276 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 29 = false ∨ valuation q 71 = false ∨ valuation q 92 = false := by
  rw [value29, value71, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (84 : Vertex) (276 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 29 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value29, value89, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (84 : Vertex) (342 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 29 = false ∨ valuation q 92 = false ∨ valuation q 104 = false := by
  rw [value29, value89, value92, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (84 : Vertex) (348 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 71 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value71, value89, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (276 : Vertex) (342 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 71 = false ∨ valuation q 92 = false ∨ valuation q 104 = false := by
  rw [value71, value89, value92, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (276 : Vertex) (348 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 199 = true ∨ valuation q 29 = true ∨ valuation q 71 = true ∨ valuation q 92 = true ∨ valuation q 104 = true := by
  rw [value29, value71, value89, value92, value104, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(84 : Vertex), (276 : Vertex), (348 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (342 : Vertex) [(84 : Vertex), (276 : Vertex), (348 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 199 = true ∨ valuation q 29 = true ∨ valuation q 71 = true ∨ valuation q 90 = true ∨ valuation q 104 = true := by
  rw [value29, value71, value89, value90, value104, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(84 : Vertex), (276 : Vertex), (342 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (348 : Vertex) [(84 : Vertex), (276 : Vertex), (342 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 80 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value80, value87, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (326 : Vertex) (338 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 80 = false ∨ valuation q 87 = false ∨ valuation q 94 = false := by
  rw [value80, value87, value90, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (326 : Vertex) (338 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E183.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112183
