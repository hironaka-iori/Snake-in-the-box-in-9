import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 113 = true ∨ valuation q 6 = true ∨ valuation q 16 = true := by
  rw [value6, value7, value16, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (9 : Vertex) → w ∈ [(10 : Vertex), (27 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (9 : Vertex) [(10 : Vertex), (27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 113 = true ∨ valuation q 5 = true ∨ valuation q 16 = true := by
  rw [value5, value7, value16, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(9 : Vertex), (27 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (10 : Vertex) [(9 : Vertex), (27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 113 = true ∨ valuation q 5 = true ∨ valuation q 6 = true := by
  rw [value5, value6, value7, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(9 : Vertex), (10 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (27 : Vertex) [(9 : Vertex), (10 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 3 = true ∨ valuation q 6 = true ∨ valuation q 24 = true := by
  rw [value3, value6, value8, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ∈ [(6 : Vertex), (10 : Vertex), (78 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (14 : Vertex) [(6 : Vertex), (10 : Vertex), (78 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 114 = true ∨ valuation q 6 = true ∨ valuation q 24 = true := by
  rw [value6, value8, value24, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(10 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (6 : Vertex) [(10 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 114 = true ∨ valuation q 3 = true ∨ valuation q 6 = true := by
  rw [value3, value6, value8, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(6 : Vertex), (10 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (78 : Vertex) [(6 : Vertex), (10 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 12 = false ∨ valuation q 16 = false ∨ valuation q 28 = false := by
  rw [value9, value12, value16, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (19 : Vertex) (23 : Vertex) (27 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 116 = true ∨ valuation q 17 = true := by
  rw [value10, value17, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (23 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (23 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 116 = true ∨ valuation q 12 = true := by
  rw [value10, value12, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(23 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (29 : Vertex) [(23 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = true ∨ valuation q 12 = true := by
  rw [value3, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ∈ [(6 : Vertex), (23 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (22 : Vertex) [(6 : Vertex), (23 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 117 = true ∨ valuation q 12 = true := by
  rw [value11, value12, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(23 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (6 : Vertex) [(23 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 117 = true ∨ valuation q 3 = true := by
  rw [value3, value11, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (23 : Vertex) → w ∈ [(6 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (23 : Vertex) [(6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = false ∨ valuation q 10 = false ∨ valuation q 11 = false := by
  rw [value9, value10, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (19 : Vertex) (21 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 15 = false := by
  rw [value4, value13, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (24 : Vertex) (8 : Vertex) (25 : Vertex) (26 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 119 = true ∨ valuation q 4 = true ∨ valuation q 15 = true := by
  rw [value4, value13, value15, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(8 : Vertex), (26 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (25 : Vertex) [(8 : Vertex), (26 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 119 = true ∨ valuation q 4 = true ∨ valuation q 14 = true := by
  rw [value4, value13, value14, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (26 : Vertex) → w ∈ [(8 : Vertex), (25 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (26 : Vertex) [(8 : Vertex), (25 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 5 = true ∨ valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 17 = true := by
  rw [value5, value13, value14, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ∈ [(9 : Vertex), (24 : Vertex), (27 : Vertex), (29 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (25 : Vertex) [(9 : Vertex), (24 : Vertex), (27 : Vertex), (29 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 120 = true ∨ valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 17 = true := by
  rw [value13, value14, value16, value17, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (9 : Vertex) → w ∈ [(24 : Vertex), (27 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (9 : Vertex) [(24 : Vertex), (27 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 120 = true ∨ valuation q 5 = true ∨ valuation q 13 = true ∨ valuation q 16 = true := by
  rw [value5, value13, value14, value16, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(9 : Vertex), (24 : Vertex), (27 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (29 : Vertex) [(9 : Vertex), (24 : Vertex), (27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = true ∨ valuation q 13 = true ∨ valuation q 16 = true := by
  rw [value6, value13, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (26 : Vertex) w → w ∈ region → w ∈ [(10 : Vertex), (24 : Vertex), (27 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (26 : Vertex) [(10 : Vertex), (24 : Vertex), (27 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 121 = true ∨ valuation q 13 = true ∨ valuation q 16 = true := by
  rw [value13, value15, value16, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (26 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(24 : Vertex), (27 : Vertex)] := by decide
  have hg := other_cover q (26 : Vertex) (10 : Vertex) [(24 : Vertex), (27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 121 = true ∨ valuation q 6 = true ∨ valuation q 16 = true := by
  rw [value6, value15, value16, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (26 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(10 : Vertex), (27 : Vertex)] := by decide
  have hg := other_cover q (26 : Vertex) (24 : Vertex) [(10 : Vertex), (27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 121 = true ∨ valuation q 6 = true ∨ valuation q 13 = true := by
  rw [value6, value13, value15, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (26 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(10 : Vertex), (24 : Vertex)] := by decide
  have hg := other_cover q (26 : Vertex) (27 : Vertex) [(10 : Vertex), (24 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 14 = false := by
  rw [value7, value9, value14, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (27 : Vertex) (11 : Vertex) (19 : Vertex) (25 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 15 = false := by
  rw [value7, value9, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (27 : Vertex) (11 : Vertex) (19 : Vertex) (26 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 15 = false := by
  rw [value7, value14, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (27 : Vertex) (11 : Vertex) (25 : Vertex) (26 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 9 = false ∨ valuation q 14 = false ∨ valuation q 15 = false := by
  rw [value9, value14, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (27 : Vertex) (19 : Vertex) (25 : Vertex) (26 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 123 = true ∨ valuation q 14 = true := by
  rw [value14, value17, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(25 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (21 : Vertex) [(25 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 123 = true ∨ valuation q 10 = true := by
  rw [value10, value17, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(21 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (25 : Vertex) [(21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 1 = false ∨ valuation q 22 = false ∨ valuation q 26 = false := by
  rw [value1, value18, value22, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (72 : Vertex) (80 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 23 = false := by
  rw [value18, value19, value20, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (64 : Vertex) (69 : Vertex) (73 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 125 = true ∨ valuation q 18 = true ∨ valuation q 23 = true := by
  rw [value18, value19, value23, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(64 : Vertex), (73 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (69 : Vertex) [(64 : Vertex), (73 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E091.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112091
