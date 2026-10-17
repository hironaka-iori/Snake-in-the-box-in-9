import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 142 = true ∨ valuation q 25 = true ∨ valuation q 75 = true := by
  rw [value25, value26, value75, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(110 : Vertex), (367 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (79 : Vertex) [(110 : Vertex), (367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 142 = true ∨ valuation q 21 = true ∨ valuation q 75 = true := by
  rw [value21, value26, value75, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (110 : Vertex) → w ∈ [(79 : Vertex), (367 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (110 : Vertex) [(79 : Vertex), (367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 142 = true ∨ valuation q 21 = true ∨ valuation q 25 = true := by
  rw [value21, value25, value26, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(79 : Vertex), (110 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (367 : Vertex) [(79 : Vertex), (110 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 143 = true ∨ valuation q 28 = true := by
  rw [value27, value28, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ≠ (97 : Vertex) → w ∈ [(121 : Vertex)] := by decide
  have hg := other_cover q (113 : Vertex) (97 : Vertex) [(121 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 143 = true ∨ valuation q 22 = true := by
  rw [value22, value27, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ≠ (121 : Vertex) → w ∈ [(97 : Vertex)] := by decide
  have hg := other_cover q (113 : Vertex) (121 : Vertex) [(97 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 27 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value27, value28, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (121 : Vertex) (113 : Vertex) (123 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 144 = true ∨ valuation q 30 = true ∨ valuation q 31 = true := by
  rw [value28, value30, value31, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (121 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(123 : Vertex), (125 : Vertex)] := by decide
  have hg := other_cover q (121 : Vertex) (113 : Vertex) [(123 : Vertex), (125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 144 = true ∨ valuation q 27 = true ∨ valuation q 31 = true := by
  rw [value27, value28, value31, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (121 : Vertex) w → w ∈ region → w ≠ (123 : Vertex) → w ∈ [(113 : Vertex), (125 : Vertex)] := by decide
  have hg := other_cover q (121 : Vertex) (123 : Vertex) [(113 : Vertex), (125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 30 = false ∨ valuation q 80 = false := by
  rw [value24, value29, value30, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (122 : Vertex) (106 : Vertex) (123 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 145 = true ∨ valuation q 30 = true ∨ valuation q 80 = true := by
  rw [value29, value30, value80, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [(123 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (106 : Vertex) [(123 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 145 = true ∨ valuation q 24 = true ∨ valuation q 80 = true := by
  rw [value24, value29, value80, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (123 : Vertex) → w ∈ [(106 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (123 : Vertex) [(106 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 146 = true ∨ valuation q 29 = true := by
  rw [value29, value30, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (123 : Vertex) w → w ∈ region → w ≠ (121 : Vertex) → w ∈ [(122 : Vertex)] := by decide
  have hg := other_cover q (123 : Vertex) (121 : Vertex) [(122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 146 = true ∨ valuation q 28 = true := by
  rw [value28, value30, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (123 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(121 : Vertex)] := by decide
  have hg := other_cover q (123 : Vertex) (122 : Vertex) [(121 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 147 = true ∨ valuation q 82 = true := by
  rw [value31, value82, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (121 : Vertex) → w ∈ [(381 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (121 : Vertex) [(381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 147 = true ∨ valuation q 28 = true := by
  rw [value28, value31, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (381 : Vertex) → w ∈ [(121 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (381 : Vertex) [(121 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 148 = true ∨ valuation q 36 = true ∨ valuation q 84 = true := by
  rw [value32, value36, value84, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(168 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (161 : Vertex) [(168 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 148 = true ∨ valuation q 33 = true ∨ valuation q 84 = true := by
  rw [value32, value33, value84, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(161 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (168 : Vertex) [(161 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 32 = false ∨ valuation q 41 = false ∨ valuation q 85 = false := by
  rw [value32, value33, value41, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (177 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 149 = true ∨ valuation q 41 = true ∨ valuation q 85 = true := by
  rw [value33, value41, value85, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(177 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (160 : Vertex) [(177 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 44 = false ∨ valuation q 89 = false := by
  rw [value34, value35, value44, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (167 : Vertex) (182 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 150 = true ∨ valuation q 35 = true ∨ valuation q 44 = true ∨ valuation q 89 = true := by
  rw [value34, value35, value44, value89, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(167 : Vertex), (182 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (174 : Vertex) [(167 : Vertex), (182 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 150 = true ∨ valuation q 35 = true ∨ valuation q 39 = true ∨ valuation q 89 = true := by
  rw [value34, value35, value39, value89, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(167 : Vertex), (174 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (182 : Vertex) [(167 : Vertex), (174 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 34 = false ∨ valuation q 40 = false ∨ valuation q 90 = false := by
  rw [value34, value35, value40, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (167 : Vertex) (166 : Vertex) (175 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 151 = true ∨ valuation q 34 = true ∨ valuation q 90 = true := by
  rw [value34, value35, value90, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(166 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (175 : Vertex) [(166 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value32, value36, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (170 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 91 = false := by
  rw [value32, value36, value37, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (170 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 32 = false ∨ valuation q 38 = false ∨ valuation q 91 = false := by
  rw [value32, value36, value38, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (172 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 91 = false := by
  rw [value36, value37, value38, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (170 : Vertex) (172 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 153 = true ∨ valuation q 39 = true ∨ valuation q 46 = true := by
  rw [value37, value39, value46, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(174 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (168 : Vertex) [(174 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 153 = true ∨ valuation q 36 = true ∨ valuation q 46 = true := by
  rw [value36, value37, value46, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(168 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (174 : Vertex) [(168 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 153 = true ∨ valuation q 36 = true ∨ valuation q 39 = true := by
  rw [value36, value37, value39, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(168 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (186 : Vertex) [(168 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 154 = true ∨ valuation q 39 = true ∨ valuation q 94 = true := by
  rw [value38, value39, value94, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(174 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (168 : Vertex) [(174 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E051.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112051
