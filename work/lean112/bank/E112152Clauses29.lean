import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value61, value62, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (353 : Vertex) (355 : Vertex) (481 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 68 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value63, value68, value102, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (357 : Vertex) (365 : Vertex) (485 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value67, value68, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (364 : Vertex) (365 : Vertex) (492 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 92 = false ∨ valuation q 102 = false ∨ valuation q 113 = false := by
  rw [value80, value92, value102, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (421 : Vertex) (437 : Vertex) (485 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 93 = false ∨ valuation q 103 = false ∨ valuation q 114 = false := by
  rw [value81, value93, value103, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (422 : Vertex) (438 : Vertex) (486 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value83, value84, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (425 : Vertex) (428 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value83, value86, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (428 : Vertex) (488 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value86, value87, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (428 : Vertex) (429 : Vertex) (492 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value98, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (481 : Vertex) (482 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 101 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value99, value101, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (481 : Vertex) (483 : Vertex) (497 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value100, value101, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (482 : Vertex) (483 : Vertex) (498 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 111 = false ∨ valuation q 114 = false := by
  rw [value100, value103, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (482 : Vertex) (486 : Vertex) (498 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value104, value105, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (488 : Vertex) (490 : Vertex) (492 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value106, value107, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (492 : Vertex) (493 : Vertex) (508 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 117 = false ∨ valuation q 119 = false := by
  rw [value106, value108, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (492 : Vertex) (494 : Vertex) (508 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 119 = false ∨ valuation q 120 = false := by
  rw [value108, value109, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (494 : Vertex) (495 : Vertex) (510 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value110, value112, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (497 : Vertex) (499 : Vertex) (501 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 118 = false ∨ valuation q 119 = false ∨ valuation q 120 = false := by
  rw [value117, value118, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (508 : Vertex) (509 : Vertex) (510 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E152.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h⟩

end
end Snake9.Regrowth.E112152
