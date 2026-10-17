import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 59 = false ∨ valuation q 67 = false ∨ valuation q 69 = false := by
  rw [value59, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (281 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 19 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value19, value65, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (31 : Vertex) (279 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 177 = true ∨ valuation q 19 = true ∨ valuation q 68 = true := by
  rw [value19, value68, value69, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(31 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (279 : Vertex) [(31 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 177 = true ∨ valuation q 19 = true ∨ valuation q 65 = true := by
  rw [value19, value65, value69, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(31 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (283 : Vertex) [(31 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 178 = true ∨ valuation q 71 = true := by
  rw [value70, value71, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(327 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (70 : Vertex) [(327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 178 = true ∨ valuation q 23 = true := by
  rw [value23, value70, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(70 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (327 : Vertex) [(70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 179 = true ∨ valuation q 74 = true := by
  rw [value71, value74, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(335 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (326 : Vertex) [(335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 179 = true ∨ valuation q 70 = true := by
  rw [value70, value71, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(326 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (335 : Vertex) [(326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 24 = false ∨ valuation q 59 = false ∨ valuation q 74 = false := by
  rw [value24, value59, value72, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (331 : Vertex) (75 : Vertex) (267 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 181 = true ∨ valuation q 74 = true := by
  rw [value73, value74, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(335 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (349 : Vertex) [(335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value71, value72, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (335 : Vertex) (327 : Vertex) (331 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 182 = true ∨ valuation q 71 = true ∨ valuation q 72 = true := by
  rw [value71, value72, value74, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(327 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (333 : Vertex) [(327 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 183 = true ∨ valuation q 26 = true ∨ valuation q 63 = true ∨ valuation q 102 = true := by
  rw [value26, value63, value75, value102, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(84 : Vertex), (276 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (348 : Vertex) [(84 : Vertex), (276 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 184 = true ∨ valuation q 75 = true := by
  rw [value75, value76, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(340 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (349 : Vertex) [(340 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 185 = true ∨ valuation q 76 = true := by
  rw [value76, value77, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(348 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (333 : Vertex) [(348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 185 = true ∨ valuation q 73 = true := by
  rw [value73, value77, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(333 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (348 : Vertex) [(333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 186 = true := by
  rw [value78, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (384 : Vertex) (400 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 55 = false ∨ valuation q 82 = false ∨ valuation q 94 = false := by
  rw [value55, value79, value82, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 94 = false := by
  rw [value79, value82, value83, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (403 : Vertex) (419 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 187 = true ∨ valuation q 55 = true ∨ valuation q 82 = true ∨ valuation q 94 = true := by
  rw [value55, value79, value82, value94, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (387 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(259 : Vertex), (403 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (387 : Vertex) (419 : Vertex) [(259 : Vertex), (403 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 187 = true ∨ valuation q 55 = true ∨ valuation q 82 = true ∨ valuation q 83 = true := by
  rw [value55, value79, value82, value83, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (387 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(259 : Vertex), (403 : Vertex), (419 : Vertex)] := by decide
  have hg := other_cover q (387 : Vertex) (451 : Vertex) [(259 : Vertex), (403 : Vertex), (419 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 62 = false ∨ valuation q 81 = false ∨ valuation q 86 = false := by
  rw [value62, value80, value81, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (272 : Vertex) (401 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 62 = false ∨ valuation q 81 = false ∨ valuation q 101 = false := by
  rw [value62, value80, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (272 : Vertex) (401 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 62 = false ∨ valuation q 86 = false ∨ valuation q 101 = false := by
  rw [value62, value80, value86, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (272 : Vertex) (432 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 86 = false ∨ valuation q 101 = false := by
  rw [value80, value81, value86, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (401 : Vertex) (432 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 189 = true ∨ valuation q 82 = true := by
  rw [value81, value82, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(403 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (400 : Vertex) [(403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 189 = true ∨ valuation q 80 = true := by
  rw [value80, value81, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(400 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (403 : Vertex) [(400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 190 = true ∨ valuation q 81 = true := by
  rw [value81, value82, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(401 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (387 : Vertex) [(401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 190 = true ∨ valuation q 79 = true := by
  rw [value79, value82, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(387 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (401 : Vertex) [(387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 35 = false ∨ valuation q 83 = false ∨ valuation q 91 = false := by
  rw [value35, value83, value85, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (419 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 193 = true ∨ valuation q 35 = true ∨ valuation q 83 = true := by
  rw [value35, value83, value85, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(171 : Vertex), (419 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (443 : Vertex) [(171 : Vertex), (419 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 194 = true ∨ valuation q 38 = true ∨ valuation q 87 = true := by
  rw [value38, value86, value87, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(176 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (400 : Vertex) [(176 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E185.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112185
