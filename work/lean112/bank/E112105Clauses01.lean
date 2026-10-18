import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 137 = true ∨ valuation q 15 = true ∨ valuation q 24 = true := by
  rw [value13, value15, value24, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(71 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (65 : Vertex) [(71 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 137 = true ∨ valuation q 12 = true ∨ valuation q 24 = true := by
  rw [value12, value13, value24, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(65 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (71 : Vertex) [(65 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 137 = true ∨ valuation q 12 = true ∨ valuation q 15 = true := by
  rw [value12, value13, value15, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(65 : Vertex), (71 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (83 : Vertex) [(65 : Vertex), (71 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 2 = false ∨ valuation q 17 = false ∨ valuation q 25 = false := by
  rw [value2, value14, value17, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (4 : Vertex) (76 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 2 = false ∨ valuation q 17 = false ∨ valuation q 49 = false := by
  rw [value2, value14, value17, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (4 : Vertex) (76 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 2 = false ∨ valuation q 25 = false ∨ valuation q 49 = false := by
  rw [value2, value14, value25, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (4 : Vertex) (84 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 49 = false := by
  rw [value14, value17, value25, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (76 : Vertex) (84 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 138 = true ∨ valuation q 17 = true ∨ valuation q 25 = true ∨ valuation q 49 = true := by
  rw [value14, value17, value25, value49, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (4 : Vertex) → w ∈ [(76 : Vertex), (84 : Vertex), (196 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (4 : Vertex) [(76 : Vertex), (84 : Vertex), (196 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 138 = true ∨ valuation q 2 = true ∨ valuation q 25 = true ∨ valuation q 49 = true := by
  rw [value2, value14, value25, value49, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(4 : Vertex), (84 : Vertex), (196 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (76 : Vertex) [(4 : Vertex), (84 : Vertex), (196 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 138 = true ∨ valuation q 2 = true ∨ valuation q 17 = true ∨ valuation q 49 = true := by
  rw [value2, value14, value17, value49, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(4 : Vertex), (76 : Vertex), (196 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (84 : Vertex) [(4 : Vertex), (76 : Vertex), (196 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 138 = true ∨ valuation q 2 = true ∨ valuation q 17 = true ∨ valuation q 25 = true := by
  rw [value2, value14, value17, value25, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (196 : Vertex) → w ∈ [(4 : Vertex), (76 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (196 : Vertex) [(4 : Vertex), (76 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 4 = false ∨ valuation q 13 = false ∨ valuation q 20 = false := by
  rw [value4, value13, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (7 : Vertex) (67 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 4 = false ∨ valuation q 13 = false ∨ valuation q 71 = false := by
  rw [value4, value13, value15, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (7 : Vertex) (67 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 140 = true ∨ valuation q 5 = true ∨ valuation q 12 = true ∨ valuation q 18 = true := by
  rw [value5, value12, value16, value18, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(9 : Vertex), (65 : Vertex), (77 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (329 : Vertex) [(9 : Vertex), (65 : Vertex), (77 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 14 = true ∨ valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 55 = true := by
  rw [value14, value17, value18, value19, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ∈ [(68 : Vertex), (77 : Vertex), (78 : Vertex), (204 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (76 : Vertex) [(68 : Vertex), (77 : Vertex), (78 : Vertex), (204 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 14 = false ∨ valuation q 18 = false ∨ valuation q 19 = false := by
  rw [value14, value17, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (68 : Vertex) (77 : Vertex) (78 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 55 = false := by
  rw [value17, value18, value19, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (77 : Vertex) (78 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 141 = true ∨ valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 55 = true := by
  rw [value17, value18, value19, value55, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(77 : Vertex), (78 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (68 : Vertex) [(77 : Vertex), (78 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 141 = true ∨ valuation q 14 = true ∨ valuation q 19 = true ∨ valuation q 55 = true := by
  rw [value14, value17, value19, value55, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (77 : Vertex) → w ∈ [(68 : Vertex), (78 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (77 : Vertex) [(68 : Vertex), (78 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 141 = true ∨ valuation q 14 = true ∨ valuation q 18 = true ∨ valuation q 55 = true := by
  rw [value14, value17, value18, value55, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(68 : Vertex), (77 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (78 : Vertex) [(68 : Vertex), (77 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 141 = true ∨ valuation q 14 = true ∨ valuation q 18 = true ∨ valuation q 19 = true := by
  rw [value14, value17, value18, value19, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(68 : Vertex), (77 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (204 : Vertex) [(68 : Vertex), (77 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 20 = false := by
  rw [value16, value17, value18, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (77 : Vertex) (73 : Vertex) (76 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 27 = false := by
  rw [value16, value17, value18, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (77 : Vertex) (73 : Vertex) (76 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 20 = false ∨ valuation q 27 = false := by
  rw [value16, value18, value20, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (77 : Vertex) (73 : Vertex) (79 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 27 = false := by
  rw [value17, value18, value20, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (77 : Vertex) (76 : Vertex) (79 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 142 = true ∨ valuation q 17 = true ∨ valuation q 20 = true ∨ valuation q 27 = true := by
  rw [value17, value18, value20, value27, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (77 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(76 : Vertex), (79 : Vertex), (93 : Vertex)] := by decide
  have hg := other_cover q (77 : Vertex) (73 : Vertex) [(76 : Vertex), (79 : Vertex), (93 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 142 = true ∨ valuation q 16 = true ∨ valuation q 20 = true ∨ valuation q 27 = true := by
  rw [value16, value18, value20, value27, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (77 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(73 : Vertex), (79 : Vertex), (93 : Vertex)] := by decide
  have hg := other_cover q (77 : Vertex) (76 : Vertex) [(73 : Vertex), (79 : Vertex), (93 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 142 = true ∨ valuation q 16 = true ∨ valuation q 17 = true ∨ valuation q 27 = true := by
  rw [value16, value17, value18, value27, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (77 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(73 : Vertex), (76 : Vertex), (93 : Vertex)] := by decide
  have hg := other_cover q (77 : Vertex) (79 : Vertex) [(73 : Vertex), (76 : Vertex), (93 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 142 = true ∨ valuation q 16 = true ∨ valuation q 17 = true ∨ valuation q 20 = true := by
  rw [value16, value17, value18, value20, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (77 : Vertex) w → w ∈ region → w ≠ (93 : Vertex) → w ∈ [(73 : Vertex), (76 : Vertex), (79 : Vertex)] := by decide
  have hg := other_cover q (77 : Vertex) (93 : Vertex) [(73 : Vertex), (76 : Vertex), (79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 28 = false := by
  rw [value17, value19, value20, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (76 : Vertex) (79 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 56 = false := by
  rw [value17, value19, value20, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (76 : Vertex) (79 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 74 = false := by
  rw [value17, value19, value20, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (76 : Vertex) (79 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E105.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112105
