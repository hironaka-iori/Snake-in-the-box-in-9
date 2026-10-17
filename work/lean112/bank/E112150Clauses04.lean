import E112150Semantics
import B112E150Inputs
namespace Snake9.Regrowth.E112150
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 170 = false := by
  rw [value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (362 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 172 = false := by
  rw [value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (367 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 173 = false := by
  rw [value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (369 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 174 = false := by
  rw [value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (372 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 176 = false := by
  rw [value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (376 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 181 = false := by
  rw [value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (386 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 186 = false := by
  rw [value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (397 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 187 = false := by
  rw [value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (398 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 190 = false := by
  rw [value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (403 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 191 = false := by
  rw [value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (405 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 193 = false := by
  rw [value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (409 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 198 = false := by
  rw [value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (451 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 200 = false := by
  rw [value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (453 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 202 = false := by
  rw [value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (463 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 204 = false := by
  rw [value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (465 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 205 = false := by
  rw [value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (468 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 209 = false := by
  rw [value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (501 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause146 (q : Nat → Bool) : valuationOf q 166 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [166]) + (countLit q [167]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167])
  have hm := merge_left (literal (valuationOf q) (166)) (literal (valuationOf q) (325)) (countLit q [166]) (countLit q [167]) (count325 q) 1 (meaning166 q) (meaning325 q) hs
  change valuationOf q 166 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 325 = true := counterClause146 (baseVal q)

theorem counterClause147 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [165]) + (countLit q [166, 167]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166, 167])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [165]) (countLit q [166, 167]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause147 (baseVal q)

theorem counterClause148 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [168]) + (countLit q [169]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [169])
  have hm := merge_right (literal (valuationOf q) (169)) (literal (valuationOf q) (329)) (countLit q [168]) (countLit q [169]) (count329 q) 1 (meaning169 q) (meaning329 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 329 = true := counterClause148 (baseVal q)

theorem counterClause149 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [168]) + (countLit q [169]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [169])
  have hm := merge_left (literal (valuationOf q) (168)) (literal (valuationOf q) (329)) (countLit q [168]) (countLit q [169]) (count329 q) 1 (meaning168 q) (meaning329 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 329 = true := counterClause149 (baseVal q)

theorem counterClause150 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_right (literal (valuationOf q) (171)) (literal (valuationOf q) (331)) (countLit q [170]) (countLit q [171]) (count331 q) 1 (meaning171 q) (meaning331 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 331 = true := counterClause150 (baseVal q)

theorem counterClause151 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [168, 169]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [168, 169]) (l₂ := [170, 171])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [168, 169]) (countLit q [170, 171]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause151 (baseVal q)

theorem counterClause152 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [168, 169]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [168, 169]) (l₂ := [170, 171])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (333)) (countLit q [168, 169]) (countLit q [170, 171]) (count333 q) 1 (meaning329 q) (meaning333 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 333 = true := counterClause152 (baseVal q)

theorem counterClause153 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [165, 166, 167]) + (countLit q [168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167]) (l₂ := [168, 169, 170, 171])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [165, 166, 167]) (countLit q [168, 169, 170, 171]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause153 (baseVal q)

theorem counterClause154 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [165, 166, 167]) + (countLit q [168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167]) (l₂ := [168, 169, 170, 171])
  have hm := merge_left (literal (valuationOf q) (327)) (literal (valuationOf q) (335)) (countLit q [165, 166, 167]) (countLit q [168, 169, 170, 171]) (count335 q) 1 (meaning327 q) (meaning335 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 335 = true := counterClause154 (baseVal q)

theorem counterClause155 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171])
  have hm := merge_right (literal (valuationOf q) (335)) (literal (valuationOf q) (337)) (countLit q [159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171]) (count337 q) 1 (meaning335 q) (meaning337 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 337 = true := counterClause155 (baseVal q)

theorem counterClause156 (q : Nat → Bool) : valuationOf q 177 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [176]) + (countLit q [177]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177])
  have hm := merge_right (literal (valuationOf q) (177)) (literal (valuationOf q) (343)) (countLit q [176]) (countLit q [177]) (count343 q) 1 (meaning177 q) (meaning343 q) hs
  change valuationOf q 177 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 343 = true := counterClause156 (baseVal q)

theorem counterClause157 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176, 177])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [175]) (countLit q [176, 177]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause157 (baseVal q)

theorem counterClause158 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176, 177])
  have hm := merge_left (literal (valuationOf q) (175)) (literal (valuationOf q) (345)) (countLit q [175]) (countLit q [176, 177]) (count345 q) 1 (meaning175 q) (meaning345 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 345 = true := counterClause158 (baseVal q)

theorem counterClause159 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [172, 173, 174]) + (countLit q [175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174]) (l₂ := [175, 176, 177])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [172, 173, 174]) (countLit q [175, 176, 177]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause159 (baseVal q)

theorem counterClause160 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [172, 173, 174, 175, 176, 177]) + (countLit q [179, 180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174, 175, 176, 177]) (l₂ := [179, 180, 181, 182, 183, 184, 185])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (361)) (countLit q [172, 173, 174, 175, 176, 177]) (countLit q [179, 180, 181, 182, 183, 184, 185]) (count361 q) 1 (meaning347 q) (meaning361 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 361 = true := counterClause160 (baseVal q)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E150.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112150
