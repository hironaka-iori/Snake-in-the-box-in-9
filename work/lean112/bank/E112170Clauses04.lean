import E112170Semantics
import B112E170Inputs
namespace Snake9.Regrowth.E112170
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 104 = false := by
  rw [value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (28 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 107 = false := by
  rw [value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (67 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 109 = false := by
  rw [value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (74 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 110 = false := by
  rw [value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (76 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 121 = false := by
  rw [value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (161 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 122 = false := by
  rw [value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (162 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 125 = false := by
  rw [value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (171 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 126 = false := by
  rw [value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (173 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 131 = false := by
  rw [value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (179 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 132 = false := by
  rw [value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (182 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 140 = false := by
  rw [value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (208 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 142 = false := by
  rw [value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (211 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 143 = false := by
  rw [value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (227 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 144 = false := by
  rw [value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (229 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 147 = false := by
  rw [value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (244 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 149 = false := by
  rw [value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (247 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 151 = false := by
  rw [value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (251 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 155 = false := by
  rw [value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (355 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 169 = false := by
  rw [value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (419 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 172 = false := by
  rw [value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (426 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 174 = false := by
  rw [value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (428 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 176 = false := by
  rw [value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (436 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 178 = false := by
  rw [value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (439 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 179 = false := by
  rw [value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (440 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 186 = false := by
  rw [value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (453 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 187 = false := by
  rw [value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (458 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 189 = false := by
  rw [value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (460 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 192 = false := by
  rw [value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (468 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 194 = false := by
  rw [value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (471 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 195 = false := by
  rw [value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (472 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 197 = false := by
  rw [value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (475 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause160 (q : Nat → Bool) : valuationOf q 100 = false ∨ valuationOf q 201 = true := by
  have hs : count201 q = (countLit q [100]) + (countLit q [101, 102]) := List.countP_append (p := literal q) (l₁ := [100]) (l₂ := [101, 102])
  have hm := merge_left (literal (valuationOf q) (100)) (literal (valuationOf q) (201)) (countLit q [100]) (countLit q [101, 102]) (count201 q) 1 (meaning100 q) (meaning201 q) hs
  change valuationOf q 100 = false ∨ valuationOf q 201 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 201 = true := counterClause160 (baseVal q)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E170.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112170
