import E112179Semantics
import B112E179Inputs
namespace Snake9.Regrowth.E112179
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 198 = false := by
  rw [value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (489 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 200 = false := by
  rw [value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (495 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 201 = false := by
  rw [value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (497 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 202 = false := by
  rw [value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (498 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 207 = false := by
  rw [value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (509 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 208 = false := by
  rw [value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (510 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause199 (q : Nat → Bool) : valuationOf q 106 = false ∨ valuationOf q 209 = true := by
  have hs : count209 q = (countLit q [106]) + (countLit q [107]) := List.countP_append (p := literal q) (l₁ := [106]) (l₂ := [107])
  have hm := merge_left (literal (valuationOf q) (106)) (literal (valuationOf q) (209)) (countLit q [106]) (countLit q [107]) (count209 q) 1 (meaning106 q) (meaning209 q) hs
  change valuationOf q 106 = false ∨ valuationOf q 209 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 209 = true := counterClause199 (baseVal q)

theorem counterClause200 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 211 = true := by
  have hs : count211 q = (countLit q [105]) + (countLit q [106, 107]) := List.countP_append (p := literal q) (l₁ := [105]) (l₂ := [106, 107])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (211)) (countLit q [105]) (countLit q [106, 107]) (count211 q) 1 (meaning209 q) (meaning211 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 211 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 211 = true := counterClause200 (baseVal q)

theorem counterClause201 (q : Nat → Bool) : valuationOf q 110 = false ∨ valuationOf q 213 = true := by
  have hs : count213 q = (countLit q [109]) + (countLit q [110]) := List.countP_append (p := literal q) (l₁ := [109]) (l₂ := [110])
  have hm := merge_right (literal (valuationOf q) (110)) (literal (valuationOf q) (213)) (countLit q [109]) (countLit q [110]) (count213 q) 1 (meaning110 q) (meaning213 q) hs
  change valuationOf q 110 = false ∨ valuationOf q 213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 213 = true := counterClause201 (baseVal q)

theorem counterClause202 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 215 = true := by
  have hs : count215 q = (countLit q [108]) + (countLit q [109, 110]) := List.countP_append (p := literal q) (l₁ := [108]) (l₂ := [109, 110])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (215)) (countLit q [108]) (countLit q [109, 110]) (count215 q) 1 (meaning213 q) (meaning215 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 215 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 215 = true := counterClause202 (baseVal q)

theorem counterClause203 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [105, 106, 107]) + (countLit q [108, 109, 110]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107]) (l₂ := [108, 109, 110])
  have hm := merge_right (literal (valuationOf q) (215)) (literal (valuationOf q) (217)) (countLit q [105, 106, 107]) (countLit q [108, 109, 110]) (count217 q) 1 (meaning215 q) (meaning217 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 217 = true := counterClause203 (baseVal q)

theorem counterClause204 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [105, 106, 107]) + (countLit q [108, 109, 110]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107]) (l₂ := [108, 109, 110])
  have hm := merge_left (literal (valuationOf q) (211)) (literal (valuationOf q) (217)) (countLit q [105, 106, 107]) (countLit q [108, 109, 110]) (count217 q) 1 (meaning211 q) (meaning217 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 217 = true := counterClause204 (baseVal q)

theorem counterClause205 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 215 = false ∨ valuationOf q 218 = true := by
  have hs : count217 q = (countLit q [105, 106, 107]) + (countLit q [108, 109, 110]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107]) (l₂ := [108, 109, 110])
  have hm := merge_two (literal (valuationOf q) (211)) (literal (valuationOf q) (215)) (literal (valuationOf q) (218)) (countLit q [105, 106, 107]) (countLit q [108, 109, 110]) (count217 q) 1 1 (meaning211 q) (meaning215 q) (meaning218 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 215 = false ∨ valuationOf q 218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 215 = false ∨ valuation q 218 = true := counterClause205 (baseVal q)

theorem counterClause206 (q : Nat → Bool) : valuationOf q 112 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [112]) + (countLit q [113]) := List.countP_append (p := literal q) (l₁ := [112]) (l₂ := [113])
  have hm := merge_left (literal (valuationOf q) (112)) (literal (valuationOf q) (219)) (countLit q [112]) (countLit q [113]) (count219 q) 1 (meaning112 q) (meaning219 q) hs
  change valuationOf q 112 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 219 = true := counterClause206 (baseVal q)

theorem counterClause207 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [111]) + (countLit q [112, 113]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112, 113])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (221)) (countLit q [111]) (countLit q [112, 113]) (count221 q) 1 (meaning219 q) (meaning221 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 221 = true := counterClause207 (baseVal q)

theorem counterClause208 (q : Nat → Bool) : valuationOf q 111 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [111]) + (countLit q [112, 113]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112, 113])
  have hm := merge_left (literal (valuationOf q) (111)) (literal (valuationOf q) (221)) (countLit q [111]) (countLit q [112, 113]) (count221 q) 1 (meaning111 q) (meaning221 q) hs
  change valuationOf q 111 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 221 = true := counterClause208 (baseVal q)

theorem counterClause209 (q : Nat → Bool) : valuationOf q 116 = false ∨ valuationOf q 223 = true := by
  have hs : count223 q = (countLit q [115]) + (countLit q [116]) := List.countP_append (p := literal q) (l₁ := [115]) (l₂ := [116])
  have hm := merge_right (literal (valuationOf q) (116)) (literal (valuationOf q) (223)) (countLit q [115]) (countLit q [116]) (count223 q) 1 (meaning116 q) (meaning223 q) hs
  change valuationOf q 116 = false ∨ valuationOf q 223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 223 = true := counterClause209 (baseVal q)

theorem counterClause210 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [114]) + (countLit q [115, 116]) := List.countP_append (p := literal q) (l₁ := [114]) (l₂ := [115, 116])
  have hm := merge_right (literal (valuationOf q) (223)) (literal (valuationOf q) (225)) (countLit q [114]) (countLit q [115, 116]) (count225 q) 1 (meaning223 q) (meaning225 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 225 = true := counterClause210 (baseVal q)

theorem counterClause211 (q : Nat → Bool) : valuationOf q 114 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [114]) + (countLit q [115, 116]) := List.countP_append (p := literal q) (l₁ := [114]) (l₂ := [115, 116])
  have hm := merge_left (literal (valuationOf q) (114)) (literal (valuationOf q) (225)) (countLit q [114]) (countLit q [115, 116]) (count225 q) 1 (meaning114 q) (meaning225 q) hs
  change valuationOf q 114 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 225 = true := counterClause211 (baseVal q)

theorem counterClause212 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [111, 112, 113]) + (countLit q [114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113]) (l₂ := [114, 115, 116])
  have hm := merge_right (literal (valuationOf q) (225)) (literal (valuationOf q) (227)) (countLit q [111, 112, 113]) (countLit q [114, 115, 116]) (count227 q) 1 (meaning225 q) (meaning227 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 227 = true := counterClause212 (baseVal q)

theorem counterClause213 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [111, 112, 113]) + (countLit q [114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113]) (l₂ := [114, 115, 116])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (227)) (countLit q [111, 112, 113]) (countLit q [114, 115, 116]) (count227 q) 1 (meaning221 q) (meaning227 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 227 = true := counterClause213 (baseVal q)

theorem counterClause214 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 225 = false ∨ valuationOf q 228 = true := by
  have hs : count227 q = (countLit q [111, 112, 113]) + (countLit q [114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113]) (l₂ := [114, 115, 116])
  have hm := merge_two (literal (valuationOf q) (221)) (literal (valuationOf q) (225)) (literal (valuationOf q) (228)) (countLit q [111, 112, 113]) (countLit q [114, 115, 116]) (count227 q) 1 1 (meaning221 q) (meaning225 q) (meaning228 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 225 = false ∨ valuationOf q 228 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 225 = false ∨ valuation q 228 = true := counterClause214 (baseVal q)

theorem counterClause215 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_right (literal (valuationOf q) (227)) (literal (valuationOf q) (229)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 (meaning227 q) (meaning229 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 229 = true := counterClause215 (baseVal q)

theorem counterClause216 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 230 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_right (literal (valuationOf q) (228)) (literal (valuationOf q) (230)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 2 (meaning228 q) (meaning230 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 230 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 230 = true := counterClause216 (baseVal q)

theorem counterClause217 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (229)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 (meaning217 q) (meaning229 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 229 = true := counterClause217 (baseVal q)

theorem counterClause218 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 227 = false ∨ valuationOf q 230 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_two (literal (valuationOf q) (217)) (literal (valuationOf q) (227)) (literal (valuationOf q) (230)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 1 (meaning217 q) (meaning227 q) (meaning230 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 227 = false ∨ valuationOf q 230 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 227 = false ∨ valuation q 230 = true := counterClause218 (baseVal q)

theorem counterClause219 (q : Nat → Bool) : valuationOf q 218 = false ∨ valuationOf q 230 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_left (literal (valuationOf q) (218)) (literal (valuationOf q) (230)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 2 (meaning218 q) (meaning230 q) hs
  change valuationOf q 218 = false ∨ valuationOf q 230 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 230 = true := counterClause219 (baseVal q)

theorem counterClause220 (q : Nat → Bool) : valuationOf q 118 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [118]) + (countLit q [119]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119])
  have hm := merge_left (literal (valuationOf q) (118)) (literal (valuationOf q) (231)) (countLit q [118]) (countLit q [119]) (count231 q) 1 (meaning118 q) (meaning231 q) hs
  change valuationOf q 118 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 231 = true := counterClause220 (baseVal q)

theorem counterClause221 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118, 119])
  have hm := merge_right (literal (valuationOf q) (231)) (literal (valuationOf q) (233)) (countLit q [117]) (countLit q [118, 119]) (count233 q) 1 (meaning231 q) (meaning233 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 233 = true := counterClause221 (baseVal q)

theorem counterClause222 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [121]) + (countLit q [122]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122])
  have hm := merge_left (literal (valuationOf q) (121)) (literal (valuationOf q) (235)) (countLit q [121]) (countLit q [122]) (count235 q) 1 (meaning121 q) (meaning235 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 235 = true := counterClause222 (baseVal q)

theorem counterClause223 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121, 122])
  have hm := merge_right (literal (valuationOf q) (235)) (literal (valuationOf q) (237)) (countLit q [120]) (countLit q [121, 122]) (count237 q) 1 (meaning235 q) (meaning237 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 237 = true := counterClause223 (baseVal q)

theorem counterClause224 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause224 (baseVal q)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E179.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112179
