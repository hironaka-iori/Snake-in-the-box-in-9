import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 106 = true ∨ valuation q 2 = true := by
  rw [value1, value2, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(1 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (8 : Vertex) [(1 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 107 = true ∨ valuation q 30 = true := by
  rw [value2, value30, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(129 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (0 : Vertex) [(129 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 108 = true ∨ valuation q 10 = true := by
  rw [value3, value10, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (7 : Vertex) → w ∈ [(22 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (7 : Vertex) [(22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 108 = true ∨ valuation q 4 = true := by
  rw [value3, value4, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(7 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (22 : Vertex) [(7 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 109 = true ∨ valuation q 7 = true := by
  rw [value4, value7, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(15 : Vertex)] := by decide
  have hg := other_cover q (7 : Vertex) (6 : Vertex) [(15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 109 = true ∨ valuation q 3 = true := by
  rw [value3, value4, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(6 : Vertex)] := by decide
  have hg := other_cover q (7 : Vertex) (15 : Vertex) [(6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 110 = true ∨ valuation q 1 = true := by
  rw [value1, value5, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(0 : Vertex)] := by decide
  have hg := other_cover q (8 : Vertex) (10 : Vertex) [(0 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 111 = true ∨ valuation q 5 = true := by
  rw [value5, value6, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (26 : Vertex) → w ∈ [(8 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (26 : Vertex) [(8 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 112 = true ∨ valuation q 34 = true := by
  rw [value7, value34, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (7 : Vertex) → w ∈ [(143 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (7 : Vertex) [(143 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 112 = true ∨ valuation q 4 = true := by
  rw [value4, value7, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(7 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (143 : Vertex) [(7 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 113 = true ∨ valuation q 10 = true := by
  rw [value8, value10, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (20 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(22 : Vertex)] := by decide
  have hg := other_cover q (20 : Vertex) (21 : Vertex) [(22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 113 = true ∨ valuation q 9 = true := by
  rw [value8, value9, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (20 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(21 : Vertex)] := by decide
  have hg := other_cover q (20 : Vertex) (22 : Vertex) [(21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 114 = true ∨ valuation q 14 = true := by
  rw [value9, value14, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (20 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (20 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 114 = true ∨ valuation q 8 = true := by
  rw [value8, value9, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(20 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (29 : Vertex) [(20 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 115 = true ∨ valuation q 8 = true := by
  rw [value8, value10, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(20 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (6 : Vertex) [(20 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 115 = true ∨ valuation q 3 = true := by
  rw [value3, value10, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (20 : Vertex) → w ∈ [(6 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (20 : Vertex) [(6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 116 = true ∨ valuation q 14 = true := by
  rw [value11, value14, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (27 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 116 = true ∨ valuation q 13 = true := by
  rw [value11, value13, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(27 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (29 : Vertex) [(27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 117 = true ∨ valuation q 6 = true := by
  rw [value6, value12, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (26 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(10 : Vertex)] := by decide
  have hg := other_cover q (26 : Vertex) (27 : Vertex) [(10 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 118 = true ∨ valuation q 12 = true := by
  rw [value12, value13, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(26 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (25 : Vertex) [(26 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 118 = true ∨ valuation q 11 = true := by
  rw [value11, value13, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (26 : Vertex) → w ∈ [(25 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (26 : Vertex) [(25 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 119 = true ∨ valuation q 11 = true := by
  rw [value11, value14, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(25 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (21 : Vertex) [(25 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 119 = true ∨ valuation q 9 = true := by
  rw [value9, value14, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(21 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (25 : Vertex) [(21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 120 = true ∨ valuation q 16 = true ∨ valuation q 61 = true := by
  rw [value15, value16, value61, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (104 : Vertex) → w ∈ [(97 : Vertex), (352 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (104 : Vertex) [(97 : Vertex), (352 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 121 = true ∨ valuation q 62 = true := by
  rw [value16, value62, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (97 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(353 : Vertex)] := by decide
  have hg := other_cover q (97 : Vertex) (96 : Vertex) [(353 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 17 = false ∨ valuation q 22 = false ∨ valuation q 65 = false := by
  rw [value17, value18, value22, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (103 : Vertex) (102 : Vertex) (111 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 22 = false := by
  rw [value17, value20, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (102 : Vertex) (106 : Vertex) (111 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 127 = true ∨ valuation q 21 = true ∨ valuation q 68 = true := by
  rw [value21, value22, value68, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (103 : Vertex) → w ∈ [(110 : Vertex), (367 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (103 : Vertex) [(110 : Vertex), (367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 127 = true ∨ valuation q 18 = true ∨ valuation q 21 = true := by
  rw [value18, value21, value22, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(103 : Vertex), (110 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (367 : Vertex) [(103 : Vertex), (110 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 2 = false ∨ valuation q 32 = false ∨ valuation q 35 = false := by
  rw [value2, value30, value32, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (1 : Vertex) (137 : Vertex) (161 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 2 = false ∨ valuation q 32 = false ∨ valuation q 46 = false := by
  rw [value2, value30, value32, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (1 : Vertex) (137 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 2 = false ∨ valuation q 35 = false ∨ valuation q 46 = false := by
  rw [value2, value30, value35, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (1 : Vertex) (161 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E075.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112075
