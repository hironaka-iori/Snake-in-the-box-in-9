import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 53 = false := by
  rw [value35, value37, value38, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (176 : Vertex) (179 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 79 = false := by
  rw [value35, value37, value38, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (176 : Vertex) (179 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 53 = false ∨ valuation q 79 = false := by
  rw [value35, value37, value53, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (176 : Vertex) (242 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 53 = false ∨ valuation q 79 = false := by
  rw [value37, value38, value53, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (179 : Vertex) (242 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 139 = true ∨ valuation q 37 = true ∨ valuation q 40 = true := by
  rw [value37, value38, value40, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(178 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (177 : Vertex) [(178 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 139 = true ∨ valuation q 36 = true ∨ valuation q 40 = true := by
  rw [value36, value38, value40, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(177 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (178 : Vertex) [(177 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 139 = true ∨ valuation q 36 = true ∨ valuation q 37 = true := by
  rw [value36, value37, value38, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(177 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (187 : Vertex) [(177 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 36 = false ∨ valuation q 42 = false ∨ valuation q 81 = false := by
  rw [value36, value39, value42, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (181 : Vertex) (177 : Vertex) (189 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 140 = true ∨ valuation q 42 = true ∨ valuation q 81 = true := by
  rw [value39, value42, value81, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(189 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (177 : Vertex) [(189 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 140 = true ∨ valuation q 36 = true ∨ valuation q 42 = true := by
  rw [value36, value39, value42, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(177 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (437 : Vertex) [(177 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 141 = true ∨ valuation q 44 = true := by
  rw [value40, value44, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(191 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (179 : Vertex) [(191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 142 = true ∨ valuation q 42 = true ∨ valuation q 43 = true := by
  rw [value41, value42, value43, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(189 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (172 : Vertex) [(189 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 142 = true ∨ valuation q 31 = true ∨ valuation q 43 = true := by
  rw [value31, value41, value43, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(172 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (189 : Vertex) [(172 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 142 = true ∨ valuation q 31 = true ∨ valuation q 42 = true := by
  rw [value31, value41, value42, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(172 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (190 : Vertex) [(172 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value32, value39, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (181 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 44 = false := by
  rw [value32, value39, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (181 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 59 = false := by
  rw [value32, value39, value42, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (181 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 32 = false ∨ valuation q 41 = false ∨ valuation q 44 = false := by
  rw [value32, value41, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 32 = false ∨ valuation q 44 = false ∨ valuation q 59 = false := by
  rw [value32, value42, value44, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (191 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 44 = false := by
  rw [value39, value41, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (181 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 59 = false := by
  rw [value39, value41, value42, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (181 : Vertex) (188 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 39 = false ∨ valuation q 44 = false ∨ valuation q 59 = false := by
  rw [value39, value42, value44, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (181 : Vertex) (191 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 41 = false ∨ valuation q 44 = false ∨ valuation q 59 = false := by
  rw [value41, value42, value44, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (188 : Vertex) (191 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 33 = false ∨ valuation q 41 = false ∨ valuation q 44 = false := by
  rw [value33, value41, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (174 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 144 = true ∨ valuation q 33 = true ∨ valuation q 44 = true := by
  rw [value33, value43, value44, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(174 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (188 : Vertex) [(174 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 34 = false ∨ valuation q 40 = false ∨ valuation q 42 = false := by
  rw [value34, value40, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (187 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 34 = false ∨ valuation q 40 = false ∨ valuation q 43 = false := by
  rw [value34, value40, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (187 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 145 = true ∨ valuation q 34 = true ∨ valuation q 42 = true ∨ valuation q 43 = true := by
  rw [value34, value42, value43, value44, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (191 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(175 : Vertex), (189 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (191 : Vertex) (187 : Vertex) [(175 : Vertex), (189 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 146 = true := by
  rw [value45, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (205 : Vertex) (221 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 17 = false ∨ valuation q 49 = false ∨ valuation q 92 = false := by
  rw [value17, value46, value49, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (222 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 92 = false := by
  rw [value46, value49, value52, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (222 : Vertex) (238 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 148 = true ∨ valuation q 49 = true := by
  rw [value47, value49, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (221 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E154.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112154
