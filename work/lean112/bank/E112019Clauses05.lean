import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 161 = true ∨ valuation q 44 = true ∨ valuation q 99 = true := by
  rw [value40, value44, value99, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(200 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (193 : Vertex) [(200 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 161 = true ∨ valuation q 41 = true ∨ valuation q 99 = true := by
  rw [value40, value41, value99, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(193 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (200 : Vertex) [(193 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 161 = true ∨ valuation q 41 = true ∨ valuation q 44 = true := by
  rw [value40, value41, value44, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(193 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (448 : Vertex) [(193 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 41 = true := by
  rw [value41, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (193 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 40 = true ∨ valuation q 45 = true ∨ valuation q 100 = true := by
  rw [value40, value41, value45, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ∈ [(192 : Vertex), (201 : Vertex), (449 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (193 : Vertex) [(192 : Vertex), (201 : Vertex), (449 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 40 = false ∨ valuation q 45 = false ∨ valuation q 100 = false := by
  rw [value40, value41, value45, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (192 : Vertex) (201 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 40 = false ∨ valuation q 45 = false := by
  rw [value40, value45, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (193 : Vertex) (192 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 45 = false ∨ valuation q 100 = false := by
  rw [value45, value100, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (193 : Vertex) (201 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 162 = true ∨ valuation q 45 = true ∨ valuation q 100 = true := by
  rw [value41, value45, value100, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(201 : Vertex), (449 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (192 : Vertex) [(201 : Vertex), (449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 162 = true ∨ valuation q 40 = true ∨ valuation q 100 = true := by
  rw [value40, value41, value100, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(192 : Vertex), (449 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (201 : Vertex) [(192 : Vertex), (449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 162 = true ∨ valuation q 40 = true ∨ valuation q 45 = true := by
  rw [value40, value41, value45, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(192 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (449 : Vertex) [(192 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value42, value43, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (199 : Vertex) (206 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 163 = true ∨ valuation q 48 = true ∨ valuation q 52 = true := by
  rw [value42, value48, value52, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(206 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (199 : Vertex) [(206 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 163 = true ∨ valuation q 43 = true ∨ valuation q 52 = true := by
  rw [value42, value43, value52, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(199 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (206 : Vertex) [(199 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 163 = true ∨ valuation q 43 = true ∨ valuation q 48 = true := by
  rw [value42, value43, value48, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(199 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (214 : Vertex) [(199 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 10 = true ∨ valuation q 27 = true ∨ valuation q 42 = true ∨ valuation q 53 = true ∨ valuation q 104 = true := by
  rw [value10, value27, value42, value43, value53, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ∈ [(71 : Vertex), (135 : Vertex), (198 : Vertex), (215 : Vertex), (455 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (199 : Vertex) [(71 : Vertex), (135 : Vertex), (198 : Vertex), (215 : Vertex), (455 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 10 = false ∨ valuation q 42 = false ∨ valuation q 104 = false := by
  rw [value10, value42, value43, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (71 : Vertex) (198 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 27 = false ∨ valuation q 42 = false ∨ valuation q 104 = false := by
  rw [value27, value42, value43, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (135 : Vertex) (198 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 42 = false ∨ valuation q 53 = false ∨ valuation q 104 = false := by
  rw [value42, value43, value53, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (198 : Vertex) (215 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 164 = true ∨ valuation q 27 = true ∨ valuation q 42 = true ∨ valuation q 53 = true ∨ valuation q 104 = true := by
  rw [value27, value42, value43, value53, value104, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(135 : Vertex), (198 : Vertex), (215 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (71 : Vertex) [(135 : Vertex), (198 : Vertex), (215 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 164 = true ∨ valuation q 10 = true ∨ valuation q 42 = true ∨ valuation q 53 = true ∨ valuation q 104 = true := by
  rw [value10, value42, value43, value53, value104, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(71 : Vertex), (198 : Vertex), (215 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (135 : Vertex) [(71 : Vertex), (198 : Vertex), (215 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 164 = true ∨ valuation q 10 = true ∨ valuation q 27 = true ∨ valuation q 53 = true ∨ valuation q 104 = true := by
  rw [value10, value27, value43, value53, value104, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(71 : Vertex), (135 : Vertex), (215 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (198 : Vertex) [(71 : Vertex), (135 : Vertex), (215 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 164 = true ∨ valuation q 10 = true ∨ valuation q 27 = true ∨ valuation q 42 = true ∨ valuation q 104 = true := by
  rw [value10, value27, value42, value43, value104, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(71 : Vertex), (135 : Vertex), (198 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (215 : Vertex) [(71 : Vertex), (135 : Vertex), (198 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 164 = true ∨ valuation q 10 = true ∨ valuation q 27 = true ∨ valuation q 42 = true ∨ valuation q 53 = true := by
  rw [value10, value27, value42, value43, value53, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(71 : Vertex), (135 : Vertex), (198 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (455 : Vertex) [(71 : Vertex), (135 : Vertex), (198 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 40 = true ∨ valuation q 45 = true ∨ valuation q 47 = true ∨ valuation q 105 = true := by
  rw [value40, value44, value45, value47, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ∈ [(192 : Vertex), (201 : Vertex), (204 : Vertex), (456 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (200 : Vertex) [(192 : Vertex), (201 : Vertex), (204 : Vertex), (456 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 40 = false ∨ valuation q 47 = false ∨ valuation q 105 = false := by
  rw [value40, value44, value47, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (192 : Vertex) (204 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 105 = false := by
  rw [value44, value45, value47, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (201 : Vertex) (204 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 165 = true ∨ valuation q 45 = true ∨ valuation q 47 = true ∨ valuation q 105 = true := by
  rw [value44, value45, value47, value105, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(201 : Vertex), (204 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (192 : Vertex) [(201 : Vertex), (204 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 165 = true ∨ valuation q 40 = true ∨ valuation q 47 = true ∨ valuation q 105 = true := by
  rw [value40, value44, value47, value105, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(192 : Vertex), (204 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (201 : Vertex) [(192 : Vertex), (204 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 165 = true ∨ valuation q 40 = true ∨ valuation q 45 = true ∨ valuation q 105 = true := by
  rw [value40, value44, value45, value105, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(192 : Vertex), (201 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (204 : Vertex) [(192 : Vertex), (201 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 165 = true ∨ valuation q 40 = true ∨ valuation q 45 = true ∨ valuation q 47 = true := by
  rw [value40, value44, value45, value47, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(192 : Vertex), (201 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (456 : Vertex) [(192 : Vertex), (201 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 41 = false ∨ valuation q 44 = false ∨ valuation q 46 = false := by
  rw [value41, value44, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E019.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112019
