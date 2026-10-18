import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 137 = true ∨ valuation q 20 = true ∨ valuation q 26 = true := by
  rw [value20, value21, value26, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(149 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (135 : Vertex) [(149 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 137 = true ∨ valuation q 12 = true ∨ valuation q 26 = true := by
  rw [value12, value21, value26, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(135 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (149 : Vertex) [(135 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 14 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value14, value22, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (137 : Vertex) (155 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 14 = false ∨ valuation q 24 = false ∨ valuation q 94 = false := by
  rw [value14, value22, value24, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (137 : Vertex) (155 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 95 = false := by
  rw [value15, value23, value24, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (155 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 26 = false := by
  rw [value22, value23, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (153 : Vertex) (154 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 23 = true ∨ valuation q 26 = true := by
  rw [value23, value24, value26, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(154 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (153 : Vertex) [(154 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 22 = true ∨ valuation q 26 = true := by
  rw [value22, value24, value26, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(153 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (154 : Vertex) [(153 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 22 = true ∨ valuation q 23 = true := by
  rw [value22, value23, value24, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(153 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (159 : Vertex) [(153 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value21, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (159 : Vertex) (151 : Vertex) (155 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 142 = true ∨ valuation q 21 = true ∨ valuation q 25 = true := by
  rw [value21, value25, value26, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(151 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (155 : Vertex) [(151 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 35 = false := by
  rw [value27, value28, value29, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (192 : Vertex) (197 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 28 = false ∨ valuation q 30 = false ∨ valuation q 33 = false := by
  rw [value28, value29, value30, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 28 = false ∨ valuation q 30 = false ∨ valuation q 102 = false := by
  rw [value28, value29, value30, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (199 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 28 = false ∨ valuation q 33 = false ∨ valuation q 102 = false := by
  rw [value28, value29, value33, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (205 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 102 = false := by
  rw [value29, value30, value33, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (199 : Vertex) (205 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 146 = true ∨ valuation q 12 = true ∨ valuation q 34 = true := by
  rw [value12, value30, value34, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(135 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (197 : Vertex) [(135 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 146 = true ∨ valuation q 12 = true ∨ valuation q 29 = true := by
  rw [value12, value29, value30, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(135 : Vertex), (197 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (207 : Vertex) [(135 : Vertex), (197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 147 = true ∨ valuation q 13 = true ∨ valuation q 27 = true ∨ valuation q 32 = true := by
  rw [value13, value27, value31, value32, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(136 : Vertex), (192 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (72 : Vertex) [(136 : Vertex), (192 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 14 = false ∨ valuation q 28 = false ∨ valuation q 31 = false := by
  rw [value14, value28, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 14 = false ∨ valuation q 28 = false ∨ valuation q 33 = false := by
  rw [value14, value28, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 14 = false ∨ valuation q 28 = false ∨ valuation q 103 = false := by
  rw [value14, value28, value32, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 14 = false ∨ valuation q 31 = false ∨ valuation q 33 = false := by
  rw [value14, value31, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 28 = false ∨ valuation q 31 = false ∨ valuation q 33 = false := by
  rw [value28, value31, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 150 = true ∨ valuation q 33 = true := by
  rw [value33, value34, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(205 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (199 : Vertex) [(205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value36, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (211 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 153 = true ∨ valuation q 36 = true := by
  rw [value36, value37, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(210 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (209 : Vertex) [(210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 153 = true ∨ valuation q 35 = true := by
  rw [value35, value37, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(209 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (210 : Vertex) [(209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 42 = true := by
  rw [value40, value42, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (221 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 41 = true := by
  rw [value40, value41, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(221 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (222 : Vertex) [(221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 25 = false ∨ valuation q 33 = false ∨ valuation q 40 = false := by
  rw [value25, value33, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (157 : Vertex) (205 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 157 = true ∨ valuation q 25 = true ∨ valuation q 33 = true := by
  rw [value25, value33, value41, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(157 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (220 : Vertex) [(157 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E120.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112120
