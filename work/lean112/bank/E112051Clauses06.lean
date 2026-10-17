import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value72, value73, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (367 : Vertex) (363 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 191 = true ∨ valuation q 26 = true ∨ valuation q 57 = true ∨ valuation q 72 = true ∨ valuation q 73 = true ∨ valuation q 74 = true := by
  rw [value26, value57, value72, value73, value74, value75, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(111 : Vertex), (303 : Vertex), (363 : Vertex), (365 : Vertex), (366 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (359 : Vertex) [(111 : Vertex), (303 : Vertex), (363 : Vertex), (365 : Vertex), (366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 191 = true ∨ valuation q 26 = true ∨ valuation q 57 = true ∨ valuation q 70 = true ∨ valuation q 73 = true ∨ valuation q 74 = true := by
  rw [value26, value57, value70, value73, value74, value75, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(111 : Vertex), (303 : Vertex), (359 : Vertex), (365 : Vertex), (366 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (363 : Vertex) [(111 : Vertex), (303 : Vertex), (359 : Vertex), (365 : Vertex), (366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 192 = true ∨ valuation q 77 = true ∨ valuation q 79 = true := by
  rw [value76, value77, value79, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ≠ (352 : Vertex) → w ∈ [(370 : Vertex), (376 : Vertex)] := by decide
  have hg := other_cover q (368 : Vertex) (352 : Vertex) [(370 : Vertex), (376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 192 = true ∨ valuation q 66 = true ∨ valuation q 79 = true := by
  rw [value66, value76, value79, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ≠ (370 : Vertex) → w ∈ [(352 : Vertex), (376 : Vertex)] := by decide
  have hg := other_cover q (368 : Vertex) (370 : Vertex) [(352 : Vertex), (376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 80 = false := by
  rw [value76, value77, value78, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (370 : Vertex) (368 : Vertex) (371 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 194 = true ∨ valuation q 77 = true := by
  rw [value77, value78, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (371 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(370 : Vertex)] := by decide
  have hg := other_cover q (371 : Vertex) (355 : Vertex) [(370 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 194 = true ∨ valuation q 68 = true := by
  rw [value68, value78, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (371 : Vertex) w → w ∈ region → w ≠ (370 : Vertex) → w ∈ [(355 : Vertex)] := by decide
  have hg := other_cover q (371 : Vertex) (370 : Vertex) [(355 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 76 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value76, value79, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (368 : Vertex) (378 : Vertex) (380 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 29 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value29, value77, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (370 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 29 = false ∨ valuation q 77 = false ∨ valuation q 83 = false := by
  rw [value29, value77, value80, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (370 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 63 = false ∨ valuation q 77 = false ∨ valuation q 83 = false := by
  rw [value63, value77, value80, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (370 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value79, value81, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (380 : Vertex) (376 : Vertex) (381 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 197 = true ∨ valuation q 82 = true ∨ valuation q 83 = true := by
  rw [value81, value82, value83, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (380 : Vertex) w → w ∈ region → w ≠ (376 : Vertex) → w ∈ [(381 : Vertex), (382 : Vertex)] := by decide
  have hg := other_cover q (380 : Vertex) (376 : Vertex) [(381 : Vertex), (382 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 197 = true ∨ valuation q 79 = true ∨ valuation q 83 = true := by
  rw [value79, value81, value83, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (380 : Vertex) w → w ∈ region → w ≠ (381 : Vertex) → w ∈ [(376 : Vertex), (382 : Vertex)] := by decide
  have hg := other_cover q (380 : Vertex) (381 : Vertex) [(376 : Vertex), (382 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 31 = false ∨ valuation q 65 = false ∨ valuation q 81 = false := by
  rw [value31, value65, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (125 : Vertex) (317 : Vertex) (380 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 31 = false ∨ valuation q 73 = false ∨ valuation q 81 = false := by
  rw [value31, value73, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (125 : Vertex) (365 : Vertex) (380 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 65 = false ∨ valuation q 73 = false ∨ valuation q 81 = false := by
  rw [value65, value73, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (317 : Vertex) (365 : Vertex) (380 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 198 = true ∨ valuation q 31 = true ∨ valuation q 65 = true ∨ valuation q 73 = true := by
  rw [value31, value65, value73, value82, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (380 : Vertex) → w ∈ [(125 : Vertex), (317 : Vertex), (365 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (380 : Vertex) [(125 : Vertex), (317 : Vertex), (365 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 74 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value74, value80, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (382 : Vertex) (366 : Vertex) (378 : Vertex) (380 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 32 = false ∨ valuation q 49 = false ∨ valuation q 86 = false := by
  rw [value32, value49, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (288 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 32 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value32, value84, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (417 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 32 = false ∨ valuation q 91 = false ∨ valuation q 97 = false := by
  rw [value32, value84, value91, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (424 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 91 = false := by
  rw [value84, value85, value86, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (418 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 97 = false := by
  rw [value84, value85, value86, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (418 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 91 = false ∨ valuation q 97 = false := by
  rw [value84, value85, value91, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (424 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 91 = false ∨ valuation q 97 = false := by
  rw [value84, value86, value91, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (418 : Vertex) (424 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 202 = true ∨ valuation q 84 = true ∨ valuation q 87 = true ∨ valuation q 98 = true ∨ valuation q 107 = true := by
  rw [value84, value86, value87, value98, value107, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(416 : Vertex), (419 : Vertex), (434 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (418 : Vertex) (422 : Vertex) [(416 : Vertex), (419 : Vertex), (434 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 202 = true ∨ valuation q 84 = true ∨ valuation q 87 = true ∨ valuation q 89 = true ∨ valuation q 98 = true := by
  rw [value84, value86, value87, value89, value98, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [(416 : Vertex), (419 : Vertex), (422 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (418 : Vertex) (482 : Vertex) [(416 : Vertex), (419 : Vertex), (422 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value85, value86, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (417 : Vertex) (418 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 93 = false := by
  rw [value85, value86, value87, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (417 : Vertex) (418 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 90 = false ∨ valuation q 93 = false := by
  rw [value85, value87, value90, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (417 : Vertex) (423 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E051.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112051
