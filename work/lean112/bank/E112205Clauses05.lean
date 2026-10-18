import E112205Semantics
import B112E205Inputs
namespace Snake9.Regrowth.E112205
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 120 = false := by
  rw [value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (29 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 121 = false := by
  rw [value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (30 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 150 = false := by
  rw [value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (249 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 153 = false := by
  rw [value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (255 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 157 = false := by
  rw [value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (272 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 159 = false := by
  rw [value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (277 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 161 = false := by
  rw [value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (281 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 163 = false := by
  rw [value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (287 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 167 = false := by
  rw [value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (305 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 169 = false := by
  rw [value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (354 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 179 = false := by
  rw [value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (373 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 182 = false := by
  rw [value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (377 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 184 = false := by
  rw [value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (383 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 192 = false := by
  rw [value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (430 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 198 = false := by
  rw [value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (441 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 211 = false := by
  rw [value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (497 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 217 = false := by
  rw [value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (509 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 218 = false := by
  rw [value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (510 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause179 (q : Nat → Bool) : valuationOf q 112 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [111]) + (countLit q [112]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112])
  have hm := merge_right (literal (valuationOf q) (112)) (literal (valuationOf q) (219)) (countLit q [111]) (countLit q [112]) (count219 q) 1 (meaning112 q) (meaning219 q) hs
  change valuationOf q 112 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 219 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 111 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [111]) + (countLit q [112]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112])
  have hm := merge_left (literal (valuationOf q) (111)) (literal (valuationOf q) (219)) (countLit q [111]) (countLit q [112]) (count219 q) 1 (meaning111 q) (meaning219 q) hs
  change valuationOf q 111 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 219 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 111 = false ∨ valuationOf q 112 = false ∨ valuationOf q 220 = true := by
  have hs : count219 q = (countLit q [111]) + (countLit q [112]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112])
  have hm := merge_two (literal (valuationOf q) (111)) (literal (valuationOf q) (112)) (literal (valuationOf q) (220)) (countLit q [111]) (countLit q [112]) (count219 q) 1 1 (meaning111 q) (meaning112 q) (meaning220 q) hs
  change valuationOf q 111 = false ∨ valuationOf q 112 = false ∨ valuationOf q 220 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 220 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [110]) + (countLit q [111, 112]) := List.countP_append (p := literal q) (l₁ := [110]) (l₂ := [111, 112])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (221)) (countLit q [110]) (countLit q [111, 112]) (count221 q) 1 (meaning219 q) (meaning221 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 221 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 220 = false ∨ valuationOf q 222 = true := by
  have hs : count221 q = (countLit q [110]) + (countLit q [111, 112]) := List.countP_append (p := literal q) (l₁ := [110]) (l₂ := [111, 112])
  have hm := merge_right (literal (valuationOf q) (220)) (literal (valuationOf q) (222)) (countLit q [110]) (countLit q [111, 112]) (count221 q) 2 (meaning220 q) (meaning222 q) hs
  change valuationOf q 220 = false ∨ valuationOf q 222 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 222 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 113 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [113]) + (countLit q [114, 115]) := List.countP_append (p := literal q) (l₁ := [113]) (l₂ := [114, 115])
  have hm := merge_left (literal (valuationOf q) (113)) (literal (valuationOf q) (225)) (countLit q [113]) (countLit q [114, 115]) (count225 q) 1 (meaning113 q) (meaning225 q) hs
  change valuationOf q 113 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 225 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [110, 111, 112]) + (countLit q [113, 114, 115]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112]) (l₂ := [113, 114, 115])
  have hm := merge_right (literal (valuationOf q) (225)) (literal (valuationOf q) (227)) (countLit q [110, 111, 112]) (countLit q [113, 114, 115]) (count227 q) 1 (meaning225 q) (meaning227 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 227 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [110, 111, 112]) + (countLit q [113, 114, 115]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112]) (l₂ := [113, 114, 115])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (227)) (countLit q [110, 111, 112]) (countLit q [113, 114, 115]) (count227 q) 1 (meaning221 q) (meaning227 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 227 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 225 = false ∨ valuationOf q 228 = true := by
  have hs : count227 q = (countLit q [110, 111, 112]) + (countLit q [113, 114, 115]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112]) (l₂ := [113, 114, 115])
  have hm := merge_two (literal (valuationOf q) (221)) (literal (valuationOf q) (225)) (literal (valuationOf q) (228)) (countLit q [110, 111, 112]) (countLit q [113, 114, 115]) (count227 q) 1 1 (meaning221 q) (meaning225 q) (meaning228 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 225 = false ∨ valuationOf q 228 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 225 = false ∨ valuation q 228 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 228 = true := by
  have hs : count227 q = (countLit q [110, 111, 112]) + (countLit q [113, 114, 115]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112]) (l₂ := [113, 114, 115])
  have hm := merge_left (literal (valuationOf q) (222)) (literal (valuationOf q) (228)) (countLit q [110, 111, 112]) (countLit q [113, 114, 115]) (count227 q) 2 (meaning222 q) (meaning228 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 228 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 228 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 118 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [117]) + (countLit q [118]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118])
  have hm := merge_right (literal (valuationOf q) (118)) (literal (valuationOf q) (229)) (countLit q [117]) (countLit q [118]) (count229 q) 1 (meaning118 q) (meaning229 q) hs
  change valuationOf q 118 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 229 = true := counterClause189 (baseVal q)

theorem counterClause190 (q : Nat → Bool) : valuationOf q 117 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [117]) + (countLit q [118]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118])
  have hm := merge_left (literal (valuationOf q) (117)) (literal (valuationOf q) (229)) (countLit q [117]) (countLit q [118]) (count229 q) 1 (meaning117 q) (meaning229 q) hs
  change valuationOf q 117 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 229 = true := counterClause190 (baseVal q)

theorem counterClause191 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [116]) + (countLit q [117, 118]) := List.countP_append (p := literal q) (l₁ := [116]) (l₂ := [117, 118])
  have hm := merge_right (literal (valuationOf q) (229)) (literal (valuationOf q) (231)) (countLit q [116]) (countLit q [117, 118]) (count231 q) 1 (meaning229 q) (meaning231 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 231 = true := counterClause191 (baseVal q)

theorem counterClause192 (q : Nat → Bool) : valuationOf q 119 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [119]) + (countLit q [120]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120])
  have hm := merge_left (literal (valuationOf q) (119)) (literal (valuationOf q) (233)) (countLit q [119]) (countLit q [120]) (count233 q) 1 (meaning119 q) (meaning233 q) hs
  change valuationOf q 119 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 233 = true := counterClause192 (baseVal q)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E205.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112205
