import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 23 = false ∨ valuation q 29 = false ∨ valuation q 94 = false := by
  rw [value23, value26, value29, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (181 : Vertex) (177 : Vertex) (189 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 23 = false ∨ valuation q 45 = false ∨ valuation q 94 = false := by
  rw [value23, value26, value45, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (181 : Vertex) (177 : Vertex) (245 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 29 = false ∨ valuation q 45 = false ∨ valuation q 94 = false := by
  rw [value26, value29, value45, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (181 : Vertex) (189 : Vertex) (245 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 145 = true ∨ valuation q 25 = true ∨ valuation q 31 = true := by
  rw [value25, value27, value31, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(179 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (171 : Vertex) [(179 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 145 = true ∨ valuation q 17 = true ∨ valuation q 31 = true := by
  rw [value17, value27, value31, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(171 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (179 : Vertex) [(171 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 145 = true ∨ valuation q 17 = true ∨ valuation q 25 = true := by
  rw [value17, value25, value27, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (191 : Vertex) → w ∈ [(171 : Vertex), (179 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (191 : Vertex) [(171 : Vertex), (179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 18 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value18, value28, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (172 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 18 = false ∨ valuation q 29 = false ∨ valuation q 51 = false := by
  rw [value18, value28, value29, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (172 : Vertex) (189 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 18 = false ∨ valuation q 30 = false ∨ valuation q 51 = false := by
  rw [value18, value28, value30, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (172 : Vertex) (190 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 51 = false := by
  rw [value28, value29, value30, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (189 : Vertex) (190 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 146 = true ∨ valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 51 = true := by
  rw [value28, value29, value30, value51, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(189 : Vertex), (190 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (172 : Vertex) [(189 : Vertex), (190 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 146 = true ∨ valuation q 18 = true ∨ valuation q 30 = true ∨ valuation q 51 = true := by
  rw [value18, value28, value30, value51, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(172 : Vertex), (190 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (189 : Vertex) [(172 : Vertex), (190 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 146 = true ∨ valuation q 18 = true ∨ valuation q 29 = true ∨ valuation q 51 = true := by
  rw [value18, value28, value29, value51, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(172 : Vertex), (189 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (190 : Vertex) [(172 : Vertex), (189 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 147 = true ∨ valuation q 26 = true ∨ valuation q 28 = true ∨ valuation q 31 = true ∨ valuation q 100 = true := by
  rw [value26, value28, value29, value31, value100, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(181 : Vertex), (188 : Vertex), (191 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (173 : Vertex) [(181 : Vertex), (188 : Vertex), (191 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 147 = true ∨ valuation q 19 = true ∨ valuation q 28 = true ∨ valuation q 31 = true ∨ valuation q 100 = true := by
  rw [value19, value28, value29, value31, value100, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(173 : Vertex), (188 : Vertex), (191 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (181 : Vertex) [(173 : Vertex), (188 : Vertex), (191 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 147 = true ∨ valuation q 19 = true ∨ valuation q 26 = true ∨ valuation q 31 = true ∨ valuation q 100 = true := by
  rw [value19, value26, value29, value31, value100, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(173 : Vertex), (181 : Vertex), (191 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (188 : Vertex) [(173 : Vertex), (181 : Vertex), (191 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 147 = true ∨ valuation q 19 = true ∨ valuation q 26 = true ∨ valuation q 28 = true ∨ valuation q 31 = true := by
  rw [value19, value26, value28, value29, value31, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (445 : Vertex) → w ∈ [(173 : Vertex), (181 : Vertex), (188 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (445 : Vertex) [(173 : Vertex), (181 : Vertex), (188 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 20 = false ∨ valuation q 28 = false ∨ valuation q 52 = false := by
  rw [value20, value28, value30, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (174 : Vertex) (188 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 20 = false ∨ valuation q 31 = false ∨ valuation q 52 = false := by
  rw [value20, value30, value31, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (174 : Vertex) (191 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 148 = true ∨ valuation q 28 = true ∨ valuation q 31 = true ∨ valuation q 52 = true := by
  rw [value28, value30, value31, value52, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(188 : Vertex), (191 : Vertex), (254 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (174 : Vertex) [(188 : Vertex), (191 : Vertex), (254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 148 = true ∨ valuation q 20 = true ∨ valuation q 31 = true ∨ valuation q 52 = true := by
  rw [value20, value30, value31, value52, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(174 : Vertex), (191 : Vertex), (254 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (188 : Vertex) [(174 : Vertex), (191 : Vertex), (254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 148 = true ∨ valuation q 20 = true ∨ valuation q 28 = true ∨ valuation q 52 = true := by
  rw [value20, value28, value30, value52, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (191 : Vertex) → w ∈ [(174 : Vertex), (188 : Vertex), (254 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (191 : Vertex) [(174 : Vertex), (188 : Vertex), (254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 148 = true ∨ valuation q 20 = true ∨ valuation q 28 = true ∨ valuation q 31 = true := by
  rw [value20, value28, value30, value31, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(174 : Vertex), (188 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (254 : Vertex) [(174 : Vertex), (188 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 21 = false ∨ valuation q 27 = false ∨ valuation q 29 = false := by
  rw [value21, value27, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (187 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 21 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value21, value27, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (187 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 21 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value21, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value27, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (187 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 150 = true ∨ valuation q 34 = true ∨ valuation q 38 = true := by
  rw [value32, value34, value38, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(229 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (227 : Vertex) [(229 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 150 = true ∨ valuation q 33 = true ∨ valuation q 38 = true := by
  rw [value32, value33, value38, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(227 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (229 : Vertex) [(227 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 150 = true ∨ valuation q 33 = true ∨ valuation q 34 = true := by
  rw [value32, value33, value34, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(227 : Vertex), (229 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (233 : Vertex) [(227 : Vertex), (229 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 32 = false ∨ valuation q 36 = false ∨ valuation q 39 = false := by
  rw [value32, value33, value36, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (225 : Vertex) (231 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 151 = true ∨ valuation q 32 = true ∨ valuation q 36 = true := by
  rw [value32, value33, value36, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(225 : Vertex), (231 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (235 : Vertex) [(225 : Vertex), (231 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E159.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112159
