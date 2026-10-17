import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 38 = false ∨ valuation q 55 = false := by
  rw [value22, value23, value38, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (30 : Vertex) (95 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 38 = false ∨ valuation q 91 = false := by
  rw [value22, value23, value38, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (30 : Vertex) (95 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 55 = false ∨ valuation q 91 = false := by
  rw [value22, value23, value55, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (30 : Vertex) (159 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 38 = false ∨ valuation q 55 = false ∨ valuation q 91 = false := by
  rw [value23, value38, value55, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (95 : Vertex) (159 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 2 = false ∨ valuation q 26 = false ∨ valuation q 57 = false := by
  rw [value2, value24, value26, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (1 : Vertex) (69 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 141 = true ∨ valuation q 26 = true ∨ valuation q 57 = true := by
  rw [value24, value26, value57, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(69 : Vertex), (193 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (1 : Vertex) [(69 : Vertex), (193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 141 = true ∨ valuation q 2 = true ∨ valuation q 57 = true := by
  rw [value2, value24, value57, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(1 : Vertex), (193 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (69 : Vertex) [(1 : Vertex), (193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 141 = true ∨ valuation q 2 = true ∨ valuation q 26 = true := by
  rw [value2, value24, value26, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(1 : Vertex), (69 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (193 : Vertex) [(1 : Vertex), (69 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 142 = true ∨ valuation q 27 = true := by
  rw [value25, value27, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(70 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (69 : Vertex) [(70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 142 = true ∨ valuation q 26 = true := by
  rw [value25, value26, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(69 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (70 : Vertex) [(69 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 33 = false := by
  rw [value24, value25, value26, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (65 : Vertex) (68 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 143 = true ∨ valuation q 24 = true ∨ valuation q 33 = true := by
  rw [value24, value26, value33, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(65 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (68 : Vertex) [(65 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 143 = true ∨ valuation q 24 = true ∨ valuation q 25 = true := by
  rw [value24, value25, value26, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(65 : Vertex), (68 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (85 : Vertex) [(65 : Vertex), (68 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 144 = true ∨ valuation q 30 = true := by
  rw [value27, value30, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(78 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (68 : Vertex) [(78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 144 = true ∨ valuation q 25 = true := by
  rw [value25, value27, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(68 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (78 : Vertex) [(68 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 145 = true ∨ valuation q 29 = true ∨ valuation q 35 = true := by
  rw [value28, value29, value35, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(74 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (8 : Vertex) [(74 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 145 = true ∨ valuation q 6 = true ∨ valuation q 35 = true := by
  rw [value6, value28, value35, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(8 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (74 : Vertex) [(8 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 145 = true ∨ valuation q 6 = true ∨ valuation q 29 = true := by
  rw [value6, value28, value29, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(8 : Vertex), (74 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (88 : Vertex) [(8 : Vertex), (74 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 146 = true ∨ valuation q 30 = true := by
  rw [value29, value30, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(78 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (72 : Vertex) [(78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 146 = true ∨ valuation q 28 = true := by
  rw [value28, value29, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(72 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (78 : Vertex) [(72 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 64 = false := by
  rw [value27, value29, value30, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (70 : Vertex) (74 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 147 = true ∨ valuation q 29 = true ∨ valuation q 64 = true := by
  rw [value29, value30, value64, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(74 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (70 : Vertex) [(74 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 147 = true ∨ valuation q 27 = true ∨ valuation q 64 = true := by
  rw [value27, value30, value64, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(70 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (74 : Vertex) [(70 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 14 = false ∨ valuation q 32 = false ∨ valuation q 68 = false := by
  rw [value14, value31, value32, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (83 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 148 = true ∨ valuation q 14 = true ∨ valuation q 68 = true := by
  rw [value14, value31, value68, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(18 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (83 : Vertex) [(18 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 15 = false ∨ valuation q 31 = false ∨ valuation q 36 = false := by
  rw [value15, value31, value32, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (82 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 149 = true ∨ valuation q 15 = true ∨ valuation q 34 = true ∨ valuation q 36 = true ∨ valuation q 69 = true := by
  rw [value15, value32, value34, value36, value69, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(19 : Vertex), (87 : Vertex), (91 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (82 : Vertex) [(19 : Vertex), (87 : Vertex), (91 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 149 = true ∨ valuation q 15 = true ∨ valuation q 31 = true ∨ valuation q 36 = true ∨ valuation q 69 = true := by
  rw [value15, value31, value32, value36, value69, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(19 : Vertex), (82 : Vertex), (91 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (87 : Vertex) [(19 : Vertex), (82 : Vertex), (91 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 149 = true ∨ valuation q 15 = true ∨ valuation q 31 = true ∨ valuation q 34 = true ∨ valuation q 69 = true := by
  rw [value15, value31, value32, value34, value69, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(19 : Vertex), (82 : Vertex), (87 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (91 : Vertex) [(19 : Vertex), (82 : Vertex), (87 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 150 = true ∨ valuation q 34 = true ∨ valuation q 37 = true := by
  rw [value33, value34, value37, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(87 : Vertex), (93 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (69 : Vertex) [(87 : Vertex), (93 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 150 = true ∨ valuation q 26 = true ∨ valuation q 37 = true := by
  rw [value26, value33, value37, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(69 : Vertex), (93 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (87 : Vertex) [(69 : Vertex), (93 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 150 = true ∨ valuation q 26 = true ∨ valuation q 34 = true := by
  rw [value26, value33, value34, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (93 : Vertex) → w ∈ [(69 : Vertex), (87 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (93 : Vertex) [(69 : Vertex), (87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E115.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112115
