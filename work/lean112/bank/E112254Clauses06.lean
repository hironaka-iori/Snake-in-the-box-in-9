import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 158 = true ∨ valuation q 35 = true ∨ valuation q 40 = true := by
  rw [value35, value36, value40, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (438 : Vertex) → w ∈ [(308 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (438 : Vertex) [(308 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 32 = false ∨ valuation q 38 = false ∨ valuation q 59 = false := by
  rw [value32, value37, value38, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (312 : Vertex) (304 : Vertex) (314 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 32 = false ∨ valuation q 38 = false ∨ valuation q 97 = false := by
  rw [value32, value37, value38, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (312 : Vertex) (304 : Vertex) (314 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 59 = false ∨ valuation q 97 = false := by
  rw [value37, value38, value59, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (312 : Vertex) (314 : Vertex) (376 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 159 = true ∨ valuation q 32 = true ∨ valuation q 38 = true ∨ valuation q 59 = true := by
  rw [value32, value37, value38, value59, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (312 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(304 : Vertex), (314 : Vertex), (376 : Vertex)] := by decide
  have hg := other_cover q (312 : Vertex) (440 : Vertex) [(304 : Vertex), (314 : Vertex), (376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 21 = false ∨ valuation q 37 = false ∨ valuation q 61 = false := by
  rw [value21, value37, value38, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (314 : Vertex) (282 : Vertex) (312 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 40 = false ∨ valuation q 61 = false := by
  rw [value37, value38, value40, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (314 : Vertex) (312 : Vertex) (318 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 160 = true ∨ valuation q 37 = true ∨ valuation q 40 = true ∨ valuation q 61 = true ∨ valuation q 98 = true := by
  rw [value37, value38, value40, value61, value98, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(312 : Vertex), (318 : Vertex), (378 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (282 : Vertex) [(312 : Vertex), (318 : Vertex), (378 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 160 = true ∨ valuation q 21 = true ∨ valuation q 40 = true ∨ valuation q 61 = true ∨ valuation q 98 = true := by
  rw [value21, value38, value40, value61, value98, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (312 : Vertex) → w ∈ [(282 : Vertex), (318 : Vertex), (378 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (312 : Vertex) [(282 : Vertex), (318 : Vertex), (378 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 160 = true ∨ valuation q 21 = true ∨ valuation q 37 = true ∨ valuation q 40 = true ∨ valuation q 98 = true := by
  rw [value21, value37, value38, value40, value98, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(282 : Vertex), (312 : Vertex), (318 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (378 : Vertex) [(282 : Vertex), (312 : Vertex), (318 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 160 = true ∨ valuation q 21 = true ∨ valuation q 37 = true ∨ valuation q 40 = true ∨ valuation q 61 = true := by
  rw [value21, value37, value38, value40, value61, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(282 : Vertex), (312 : Vertex), (318 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (442 : Vertex) [(282 : Vertex), (312 : Vertex), (318 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 22 = false ∨ valuation q 41 = false ∨ valuation q 100 = false := by
  rw [value22, value39, value41, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (317 : Vertex) (285 : Vertex) (319 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 161 = true ∨ valuation q 41 = true ∨ valuation q 100 = true := by
  rw [value39, value41, value100, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (285 : Vertex) → w ∈ [(319 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (285 : Vertex) [(319 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 161 = true ∨ valuation q 22 = true ∨ valuation q 100 = true := by
  rw [value22, value39, value100, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (319 : Vertex) → w ∈ [(285 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (319 : Vertex) [(285 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 161 = true ∨ valuation q 22 = true ∨ valuation q 41 = true := by
  rw [value22, value39, value41, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (445 : Vertex) → w ∈ [(285 : Vertex), (319 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (445 : Vertex) [(285 : Vertex), (319 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 31 = false ∨ valuation q 36 = false ∨ valuation q 38 = false := by
  rw [value31, value36, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (302 : Vertex) (310 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 31 = false ∨ valuation q 36 = false ∨ valuation q 41 = false := by
  rw [value31, value36, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (302 : Vertex) (310 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 31 = false ∨ valuation q 36 = false ∨ valuation q 101 = false := by
  rw [value31, value36, value40, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (302 : Vertex) (310 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 31 = false ∨ valuation q 38 = false ∨ valuation q 41 = false := by
  rw [value31, value38, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (302 : Vertex) (314 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 31 = false ∨ valuation q 38 = false ∨ valuation q 101 = false := by
  rw [value31, value38, value40, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (302 : Vertex) (314 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 31 = false ∨ valuation q 41 = false ∨ valuation q 101 = false := by
  rw [value31, value40, value41, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (302 : Vertex) (319 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 41 = false := by
  rw [value36, value38, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (310 : Vertex) (314 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 101 = false := by
  rw [value36, value38, value40, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (310 : Vertex) (314 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 36 = false ∨ valuation q 41 = false ∨ valuation q 101 = false := by
  rw [value36, value40, value41, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (310 : Vertex) (319 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 38 = false ∨ valuation q 41 = false ∨ valuation q 101 = false := by
  rw [value38, value40, value41, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (314 : Vertex) (319 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 163 = true ∨ valuation q 39 = true ∨ valuation q 40 = true := by
  rw [value39, value40, value41, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (319 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(317 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (319 : Vertex) (287 : Vertex) [(317 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 163 = true ∨ valuation q 23 = true ∨ valuation q 40 = true := by
  rw [value23, value40, value41, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (319 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(287 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (319 : Vertex) (317 : Vertex) [(287 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 163 = true ∨ valuation q 23 = true ∨ valuation q 39 = true := by
  rw [value23, value39, value41, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (319 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(287 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (319 : Vertex) (318 : Vertex) [(287 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 44 = false ∨ valuation q 48 = false ∨ valuation q 102 = false := by
  rw [value42, value44, value48, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (324 : Vertex) (336 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 44 = false ∨ valuation q 48 = false := by
  rw [value44, value48, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (320 : Vertex) (324 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 164 = true ∨ valuation q 48 = true ∨ valuation q 102 = true := by
  rw [value42, value48, value102, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (324 : Vertex) → w ∈ [(336 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (324 : Vertex) [(336 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 45 = false ∨ valuation q 53 = false := by
  rw [value45, value53, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (323 : Vertex) (327 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E254.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112254
