import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec63 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause2017 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value91, value92, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (321 : Vertex) (322 : Vertex) (323 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2018 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value91, value92, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (321 : Vertex) (336 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2019 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value97, value99, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (332 : Vertex) (334 : Vertex) (348 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2020 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value102, value103, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (342 : Vertex) (343 : Vertex) (350 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2021 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value109, value110, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (385 : Vertex) (400 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2022 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 116 = false ∨ valuation q 124 = false ∨ valuation q 125 = false := by
  rw [value114, value116, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (396 : Vertex) (398 : Vertex) (412 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2023 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 119 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value118, value119, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (401 : Vertex) (403 : Vertex) (409 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2024 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 121 = false ∨ valuation q 123 = false ∨ valuation q 126 = false := by
  rw [value119, value121, value123, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (403 : Vertex) (407 : Vertex) (411 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block63 (q : Snake 81) (h : Conditions q) : B112E057.Block63 (valuation q) :=
  ⟨clause2017 q h, clause2018 q h, clause2019 q h, clause2020 q h, clause2021 q h, clause2022 q h, clause2023 q h, clause2024 q h⟩

end
end Snake9.Regrowth.E112057
