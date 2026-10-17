import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = true ∨ valuation q 42 = true ∨ valuation q 46 = true := by
  rw [value36, value37, value42, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ∈ [(199 : Vertex), (206 : Vertex), (214 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (198 : Vertex) [(199 : Vertex), (206 : Vertex), (214 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 42 = false ∨ valuation q 46 = false := by
  rw [value36, value37, value42, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (199 : Vertex) (206 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 21 = false ∨ valuation q 47 = false ∨ valuation q 101 = false := by
  rw [value21, value37, value47, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (135 : Vertex) (215 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 155 = true ∨ valuation q 36 = true ∨ valuation q 47 = true ∨ valuation q 101 = true := by
  rw [value36, value37, value47, value101, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(198 : Vertex), (215 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (135 : Vertex) [(198 : Vertex), (215 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 155 = true ∨ valuation q 21 = true ∨ valuation q 47 = true ∨ valuation q 101 = true := by
  rw [value21, value37, value47, value101, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(135 : Vertex), (215 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (198 : Vertex) [(135 : Vertex), (215 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 155 = true ∨ valuation q 21 = true ∨ valuation q 36 = true ∨ valuation q 101 = true := by
  rw [value21, value36, value37, value101, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(135 : Vertex), (198 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (215 : Vertex) [(135 : Vertex), (198 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 155 = true ∨ valuation q 21 = true ∨ valuation q 36 = true ∨ valuation q 47 = true := by
  rw [value21, value36, value37, value47, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(135 : Vertex), (198 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (455 : Vertex) [(135 : Vertex), (198 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 34 = false ∨ valuation q 41 = false ∨ valuation q 102 = false := by
  rw [value34, value38, value41, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (192 : Vertex) (204 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 156 = true ∨ valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 102 = true := by
  rw [value38, value39, value41, value102, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(201 : Vertex), (204 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (192 : Vertex) [(201 : Vertex), (204 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 156 = true ∨ valuation q 34 = true ∨ valuation q 41 = true ∨ valuation q 102 = true := by
  rw [value34, value38, value41, value102, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(192 : Vertex), (204 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (201 : Vertex) [(192 : Vertex), (204 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 40 = false := by
  rw [value35, value38, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 48 = false := by
  rw [value35, value38, value39, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 40 = false ∨ valuation q 48 = false := by
  rw [value35, value39, value40, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (203 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 48 = false := by
  rw [value38, value39, value40, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (200 : Vertex) (203 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 48 = true := by
  rw [value38, value39, value40, value48, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(200 : Vertex), (203 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (193 : Vertex) [(200 : Vertex), (203 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 39 = false := by
  rw [value7, value23, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (75 : Vertex) (139 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 23 = false ∨ valuation q 39 = false ∨ valuation q 103 = false := by
  rw [value23, value39, value40, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (139 : Vertex) (201 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 158 = true ∨ valuation q 7 = true ∨ valuation q 23 = true ∨ valuation q 50 = true ∨ valuation q 103 = true := by
  rw [value7, value23, value40, value50, value103, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(75 : Vertex), (139 : Vertex), (219 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (201 : Vertex) [(75 : Vertex), (139 : Vertex), (219 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 158 = true ∨ valuation q 7 = true ∨ valuation q 23 = true ∨ valuation q 39 = true ∨ valuation q 103 = true := by
  rw [value7, value23, value39, value40, value103, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(75 : Vertex), (139 : Vertex), (201 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (219 : Vertex) [(75 : Vertex), (139 : Vertex), (201 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 158 = true ∨ valuation q 7 = true ∨ valuation q 23 = true ∨ valuation q 39 = true ∨ valuation q 50 = true := by
  rw [value7, value23, value39, value40, value50, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(75 : Vertex), (139 : Vertex), (201 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (459 : Vertex) [(75 : Vertex), (139 : Vertex), (201 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 38 = false ∨ valuation q 42 = false ∨ valuation q 104 = false := by
  rw [value38, value41, value42, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (200 : Vertex) (206 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 159 = true ∨ valuation q 42 = true ∨ valuation q 104 = true := by
  rw [value41, value42, value104, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(206 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (200 : Vertex) [(206 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 159 = true ∨ valuation q 38 = true ∨ valuation q 104 = true := by
  rw [value38, value41, value104, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(200 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (206 : Vertex) [(200 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 36 = false ∨ valuation q 41 = false ∨ valuation q 106 = false := by
  rw [value36, value41, value42, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (204 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 160 = true ∨ valuation q 41 = true ∨ valuation q 106 = true := by
  rw [value41, value42, value106, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(204 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (198 : Vertex) [(204 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 160 = true ∨ valuation q 36 = true ∨ valuation q 106 = true := by
  rw [value36, value42, value106, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(198 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (204 : Vertex) [(198 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 160 = true ∨ valuation q 36 = true ∨ valuation q 41 = true := by
  rw [value36, value41, value42, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(198 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (462 : Vertex) [(198 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 110 = false := by
  rw [value43, value46, value49, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (214 : Vertex) (218 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 161 = true ∨ valuation q 49 = true ∨ valuation q 110 = true := by
  rw [value43, value49, value110, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(218 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (214 : Vertex) [(218 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 161 = true ∨ valuation q 46 = true ∨ valuation q 110 = true := by
  rw [value43, value46, value110, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(214 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (218 : Vertex) [(214 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 13 = false ∨ valuation q 29 = false ∨ valuation q 45 = false := by
  rw [value13, value29, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (148 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 13 = false ∨ valuation q 29 = false ∨ valuation q 112 = false := by
  rw [value13, value29, value44, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (148 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E110.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112110
