import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 9 = false ∨ valuation q 32 = false ∨ valuation q 40 = false := by
  rw [value9, value32, value33, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (192 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 137 = true ∨ valuation q 9 = true ∨ valuation q 32 = true ∨ valuation q 37 = true := by
  rw [value9, value32, value33, value37, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(65 : Vertex), (192 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (209 : Vertex) [(65 : Vertex), (192 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 11 = false ∨ valuation q 18 = false ∨ valuation q 35 = false := by
  rw [value11, value18, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (134 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 11 = false ∨ valuation q 35 = false ∨ valuation q 43 = false := by
  rw [value11, value34, value35, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (199 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 18 = false ∨ valuation q 35 = false ∨ valuation q 43 = false := by
  rw [value18, value34, value35, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (199 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 139 = true ∨ valuation q 19 = true ∨ valuation q 34 = true := by
  rw [value19, value34, value35, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(135 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (207 : Vertex) [(135 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 12 = true ∨ valuation q 20 = true ∨ valuation q 32 = true ∨ valuation q 37 = true := by
  rw [value12, value20, value32, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ∈ [(72 : Vertex), (136 : Vertex), (192 : Vertex), (201 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (200 : Vertex) [(72 : Vertex), (136 : Vertex), (192 : Vertex), (201 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 140 = true ∨ valuation q 20 = true ∨ valuation q 32 = true ∨ valuation q 37 = true := by
  rw [value20, value32, value36, value37, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(136 : Vertex), (192 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (72 : Vertex) [(136 : Vertex), (192 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 140 = true ∨ valuation q 12 = true ∨ valuation q 32 = true ∨ valuation q 37 = true := by
  rw [value12, value32, value36, value37, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(72 : Vertex), (192 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (136 : Vertex) [(72 : Vertex), (192 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 140 = true ∨ valuation q 12 = true ∨ valuation q 20 = true ∨ valuation q 37 = true := by
  rw [value12, value20, value36, value37, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(72 : Vertex), (136 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (192 : Vertex) [(72 : Vertex), (136 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 140 = true ∨ valuation q 12 = true ∨ valuation q 20 = true ∨ valuation q 32 = true := by
  rw [value12, value20, value32, value36, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(72 : Vertex), (136 : Vertex), (192 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (201 : Vertex) [(72 : Vertex), (136 : Vertex), (192 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 21 = false ∨ valuation q 33 = false ∨ valuation q 36 = false := by
  rw [value21, value33, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 21 = false ∨ valuation q 33 = false ∨ valuation q 38 = false := by
  rw [value21, value33, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 38 = false := by
  rw [value33, value36, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 142 = true ∨ valuation q 39 = true ∨ valuation q 46 = true := by
  rw [value38, value39, value46, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(207 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (201 : Vertex) [(207 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 142 = true ∨ valuation q 37 = true ∨ valuation q 46 = true := by
  rw [value37, value38, value46, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(201 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (207 : Vertex) [(201 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 143 = true ∨ valuation q 35 = true := by
  rw [value35, value39, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(199 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (205 : Vertex) [(199 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 144 = true ∨ valuation q 33 = true := by
  rw [value33, value40, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(193 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (211 : Vertex) [(193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value41, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (211 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 145 = true ∨ valuation q 43 = true ∨ valuation q 44 = true := by
  rw [value41, value43, value44, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(214 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (211 : Vertex) [(214 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 145 = true ∨ valuation q 42 = true ∨ valuation q 44 = true := by
  rw [value41, value42, value44, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(211 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (214 : Vertex) [(211 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 146 = true ∨ valuation q 41 = true := by
  rw [value41, value42, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(210 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (209 : Vertex) [(210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 146 = true ∨ valuation q 40 = true := by
  rw [value40, value42, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(209 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (210 : Vertex) [(209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 147 = true ∨ valuation q 34 = true ∨ valuation q 47 = true := by
  rw [value34, value43, value47, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(198 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (210 : Vertex) [(198 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 147 = true ∨ valuation q 34 = true ∨ valuation q 41 = true := by
  rw [value34, value41, value43, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(198 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (222 : Vertex) [(198 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 148 = true ∨ valuation q 41 = true ∨ valuation q 47 = true := by
  rw [value41, value44, value47, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(210 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (154 : Vertex) [(210 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 149 = true ∨ valuation q 47 = true := by
  rw [value45, value47, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (221 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 149 = true ∨ valuation q 46 = true := by
  rw [value45, value46, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(221 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (222 : Vertex) [(221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 150 = true ∨ valuation q 45 = true := by
  rw [value45, value46, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(220 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (205 : Vertex) [(220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 150 = true ∨ valuation q 38 = true := by
  rw [value38, value46, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(205 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (220 : Vertex) [(205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 45 = false := by
  rw [value43, value44, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 151 = true ∨ valuation q 43 = true ∨ valuation q 44 = true := by
  rw [value43, value44, value47, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(214 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (220 : Vertex) [(214 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E175.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112175
