import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 28 = false ∨ valuation q 76 = false := by
  rw [value19, value20, value28, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (35 : Vertex) (49 : Vertex) (161 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 28 = true ∨ valuation q 76 = true := by
  rw [value19, value28, value76, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (33 : Vertex) w → w ∈ region → w ≠ (35 : Vertex) → w ∈ [(49 : Vertex), (161 : Vertex)] := by decide
  have hg := other_cover q (33 : Vertex) (35 : Vertex) [(49 : Vertex), (161 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 20 = true ∨ valuation q 76 = true := by
  rw [value19, value20, value76, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (33 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(35 : Vertex), (161 : Vertex)] := by decide
  have hg := other_cover q (33 : Vertex) (49 : Vertex) [(35 : Vertex), (161 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 20 = true ∨ valuation q 28 = true := by
  rw [value19, value20, value28, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (33 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(35 : Vertex), (49 : Vertex)] := by decide
  have hg := other_cover q (33 : Vertex) (161 : Vertex) [(35 : Vertex), (49 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 2 = false ∨ valuation q 19 = false ∨ valuation q 78 = false := by
  rw [value2, value19, value20, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (35 : Vertex) (3 : Vertex) (33 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 2 = false ∨ valuation q 78 = false := by
  rw [value2, value78, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (35 : Vertex) (3 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 136 = true ∨ valuation q 19 = true ∨ valuation q 78 = true := by
  rw [value19, value20, value78, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (3 : Vertex) → w ∈ [(33 : Vertex), (163 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (3 : Vertex) [(33 : Vertex), (163 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 136 = true ∨ valuation q 2 = true ∨ valuation q 78 = true := by
  rw [value2, value20, value78, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(3 : Vertex), (163 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (33 : Vertex) [(3 : Vertex), (163 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 136 = true ∨ valuation q 2 = true ∨ valuation q 19 = true := by
  rw [value2, value19, value20, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(3 : Vertex), (33 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (163 : Vertex) [(3 : Vertex), (33 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 3 = false ∨ valuation q 22 = false ∨ valuation q 79 = false := by
  rw [value3, value21, value22, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (4 : Vertex) (38 : Vertex) (164 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 137 = true ∨ valuation q 22 = true ∨ valuation q 79 = true := by
  rw [value21, value22, value79, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (4 : Vertex) → w ∈ [(38 : Vertex), (164 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (4 : Vertex) [(38 : Vertex), (164 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 137 = true ∨ valuation q 3 = true ∨ valuation q 79 = true := by
  rw [value3, value21, value79, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (38 : Vertex) → w ∈ [(4 : Vertex), (164 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (38 : Vertex) [(4 : Vertex), (164 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 137 = true ∨ valuation q 3 = true ∨ valuation q 22 = true := by
  rw [value3, value21, value22, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (164 : Vertex) → w ∈ [(4 : Vertex), (38 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (164 : Vertex) [(4 : Vertex), (38 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 21 = true := by
  rw [value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (38 : Vertex) w → w ∈ region → w ∈ [(36 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (38 : Vertex) [(36 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 138 = true := by
  rw [value22, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (38 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (38 : Vertex) (36 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 5 = false ∨ valuation q 24 = false ∨ valuation q 81 = false := by
  rw [value5, value23, value24, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (8 : Vertex) (42 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 139 = true ∨ valuation q 24 = true ∨ valuation q 81 = true := by
  rw [value23, value24, value81, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(42 : Vertex), (168 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (8 : Vertex) [(42 : Vertex), (168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 139 = true ∨ valuation q 5 = true ∨ valuation q 81 = true := by
  rw [value5, value23, value81, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(8 : Vertex), (168 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (42 : Vertex) [(8 : Vertex), (168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 139 = true ∨ valuation q 5 = true ∨ valuation q 24 = true := by
  rw [value5, value23, value24, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(8 : Vertex), (42 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (168 : Vertex) [(8 : Vertex), (42 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 82 = false := by
  rw [value7, value23, value24, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (10 : Vertex) (40 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 23 = true ∨ valuation q 82 = true := by
  rw [value23, value24, value82, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(40 : Vertex), (170 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (10 : Vertex) [(40 : Vertex), (170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 7 = true ∨ valuation q 82 = true := by
  rw [value7, value24, value82, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(10 : Vertex), (170 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (40 : Vertex) [(10 : Vertex), (170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 7 = true ∨ valuation q 23 = true := by
  rw [value7, value23, value24, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(10 : Vertex), (40 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (170 : Vertex) [(10 : Vertex), (40 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 141 = true ∨ valuation q 26 = true := by
  rw [value25, value26, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (45 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(47 : Vertex)] := by decide
  have hg := other_cover q (45 : Vertex) (13 : Vertex) [(47 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 141 = true ∨ valuation q 8 = true := by
  rw [value8, value25, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (45 : Vertex) w → w ∈ region → w ≠ (47 : Vertex) → w ∈ [(13 : Vertex)] := by decide
  have hg := other_cover q (45 : Vertex) (47 : Vertex) [(13 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 142 = true ∨ valuation q 85 = true := by
  rw [value26, value85, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (47 : Vertex) w → w ∈ region → w ≠ (45 : Vertex) → w ∈ [(175 : Vertex)] := by decide
  have hg := other_cover q (47 : Vertex) (45 : Vertex) [(175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 142 = true ∨ valuation q 25 = true := by
  rw [value25, value26, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (47 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(45 : Vertex)] := by decide
  have hg := other_cover q (47 : Vertex) (175 : Vertex) [(45 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 86 = false := by
  rw [value27, value28, value29, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (48 : Vertex) (49 : Vertex) (50 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 143 = true ∨ valuation q 29 = true ∨ valuation q 86 = true := by
  rw [value27, value29, value86, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(50 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (49 : Vertex) [(50 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 143 = true ∨ valuation q 28 = true ∨ valuation q 86 = true := by
  rw [value27, value28, value86, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(49 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (50 : Vertex) [(49 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 143 = true ∨ valuation q 28 = true ∨ valuation q 29 = true := by
  rw [value27, value28, value29, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(49 : Vertex), (50 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (176 : Vertex) [(49 : Vertex), (50 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 27 = false := by
  rw [value10, value19, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (17 : Vertex) (33 : Vertex) (48 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E259.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112259
