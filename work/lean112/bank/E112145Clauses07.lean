import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 207 = false := by
  rw [value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (509 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 208 = false := by
  rw [value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (510 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause227 (q : Nat → Bool) : valuationOf q 106 = false ∨ valuationOf q 209 = true := by
  have hs : count209 q = (countLit q [106]) + (countLit q [107]) := List.countP_append (p := literal q) (l₁ := [106]) (l₂ := [107])
  have hm := merge_left (literal (valuationOf q) (106)) (literal (valuationOf q) (209)) (countLit q [106]) (countLit q [107]) (count209 q) 1 (meaning106 q) (meaning209 q) hs
  change valuationOf q 106 = false ∨ valuationOf q 209 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 209 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 211 = true := by
  have hs : count211 q = (countLit q [105]) + (countLit q [106, 107]) := List.countP_append (p := literal q) (l₁ := [105]) (l₂ := [106, 107])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (211)) (countLit q [105]) (countLit q [106, 107]) (count211 q) 1 (meaning209 q) (meaning211 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 211 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 211 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 110 = false ∨ valuationOf q 213 = true := by
  have hs : count213 q = (countLit q [109]) + (countLit q [110]) := List.countP_append (p := literal q) (l₁ := [109]) (l₂ := [110])
  have hm := merge_right (literal (valuationOf q) (110)) (literal (valuationOf q) (213)) (countLit q [109]) (countLit q [110]) (count213 q) 1 (meaning110 q) (meaning213 q) hs
  change valuationOf q 110 = false ∨ valuationOf q 213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 213 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 215 = true := by
  have hs : count215 q = (countLit q [108]) + (countLit q [109, 110]) := List.countP_append (p := literal q) (l₁ := [108]) (l₂ := [109, 110])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (215)) (countLit q [108]) (countLit q [109, 110]) (count215 q) 1 (meaning213 q) (meaning215 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 215 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 215 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [105, 106, 107]) + (countLit q [108, 109, 110]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107]) (l₂ := [108, 109, 110])
  have hm := merge_right (literal (valuationOf q) (215)) (literal (valuationOf q) (217)) (countLit q [105, 106, 107]) (countLit q [108, 109, 110]) (count217 q) 1 (meaning215 q) (meaning217 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 217 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [105, 106, 107]) + (countLit q [108, 109, 110]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107]) (l₂ := [108, 109, 110])
  have hm := merge_left (literal (valuationOf q) (211)) (literal (valuationOf q) (217)) (countLit q [105, 106, 107]) (countLit q [108, 109, 110]) (count217 q) 1 (meaning211 q) (meaning217 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 217 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 215 = false ∨ valuationOf q 218 = true := by
  have hs : count217 q = (countLit q [105, 106, 107]) + (countLit q [108, 109, 110]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107]) (l₂ := [108, 109, 110])
  have hm := merge_two (literal (valuationOf q) (211)) (literal (valuationOf q) (215)) (literal (valuationOf q) (218)) (countLit q [105, 106, 107]) (countLit q [108, 109, 110]) (count217 q) 1 1 (meaning211 q) (meaning215 q) (meaning218 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 215 = false ∨ valuationOf q 218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 215 = false ∨ valuation q 218 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 112 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [112]) + (countLit q [113]) := List.countP_append (p := literal q) (l₁ := [112]) (l₂ := [113])
  have hm := merge_left (literal (valuationOf q) (112)) (literal (valuationOf q) (219)) (countLit q [112]) (countLit q [113]) (count219 q) 1 (meaning112 q) (meaning219 q) hs
  change valuationOf q 112 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 219 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [111]) + (countLit q [112, 113]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112, 113])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (221)) (countLit q [111]) (countLit q [112, 113]) (count221 q) 1 (meaning219 q) (meaning221 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 221 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 111 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [111]) + (countLit q [112, 113]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112, 113])
  have hm := merge_left (literal (valuationOf q) (111)) (literal (valuationOf q) (221)) (countLit q [111]) (countLit q [112, 113]) (count221 q) 1 (meaning111 q) (meaning221 q) hs
  change valuationOf q 111 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 221 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 111 = false ∨ valuationOf q 219 = false ∨ valuationOf q 222 = true := by
  have hs : count221 q = (countLit q [111]) + (countLit q [112, 113]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112, 113])
  have hm := merge_two (literal (valuationOf q) (111)) (literal (valuationOf q) (219)) (literal (valuationOf q) (222)) (countLit q [111]) (countLit q [112, 113]) (count221 q) 1 1 (meaning111 q) (meaning219 q) (meaning222 q) hs
  change valuationOf q 111 = false ∨ valuationOf q 219 = false ∨ valuationOf q 222 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 219 = false ∨ valuation q 222 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 115 = false ∨ valuationOf q 223 = true := by
  have hs : count223 q = (countLit q [115]) + (countLit q [116]) := List.countP_append (p := literal q) (l₁ := [115]) (l₂ := [116])
  have hm := merge_left (literal (valuationOf q) (115)) (literal (valuationOf q) (223)) (countLit q [115]) (countLit q [116]) (count223 q) 1 (meaning115 q) (meaning223 q) hs
  change valuationOf q 115 = false ∨ valuationOf q 223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 223 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [114]) + (countLit q [115, 116]) := List.countP_append (p := literal q) (l₁ := [114]) (l₂ := [115, 116])
  have hm := merge_right (literal (valuationOf q) (223)) (literal (valuationOf q) (225)) (countLit q [114]) (countLit q [115, 116]) (count225 q) 1 (meaning223 q) (meaning225 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 225 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [111, 112, 113]) + (countLit q [114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113]) (l₂ := [114, 115, 116])
  have hm := merge_right (literal (valuationOf q) (225)) (literal (valuationOf q) (227)) (countLit q [111, 112, 113]) (countLit q [114, 115, 116]) (count227 q) 1 (meaning225 q) (meaning227 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 227 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [111, 112, 113]) + (countLit q [114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113]) (l₂ := [114, 115, 116])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (227)) (countLit q [111, 112, 113]) (countLit q [114, 115, 116]) (count227 q) 1 (meaning221 q) (meaning227 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 227 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 228 = true := by
  have hs : count227 q = (countLit q [111, 112, 113]) + (countLit q [114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113]) (l₂ := [114, 115, 116])
  have hm := merge_left (literal (valuationOf q) (222)) (literal (valuationOf q) (228)) (countLit q [111, 112, 113]) (countLit q [114, 115, 116]) (count227 q) 2 (meaning222 q) (meaning228 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 228 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 228 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_right (literal (valuationOf q) (227)) (literal (valuationOf q) (229)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 (meaning227 q) (meaning229 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 229 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 230 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_right (literal (valuationOf q) (228)) (literal (valuationOf q) (230)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 2 (meaning228 q) (meaning230 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 230 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 230 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (229)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 (meaning217 q) (meaning229 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 229 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 227 = false ∨ valuationOf q 230 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_two (literal (valuationOf q) (217)) (literal (valuationOf q) (227)) (literal (valuationOf q) (230)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 1 (meaning217 q) (meaning227 q) (meaning230 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 227 = false ∨ valuationOf q 230 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 227 = false ∨ valuation q 230 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 218 = false ∨ valuationOf q 230 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_left (literal (valuationOf q) (218)) (literal (valuationOf q) (230)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 2 (meaning218 q) (meaning230 q) hs
  change valuationOf q 218 = false ∨ valuationOf q 230 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 230 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 118 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [118]) + (countLit q [119]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119])
  have hm := merge_left (literal (valuationOf q) (118)) (literal (valuationOf q) (231)) (countLit q [118]) (countLit q [119]) (count231 q) 1 (meaning118 q) (meaning231 q) hs
  change valuationOf q 118 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 231 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118, 119])
  have hm := merge_right (literal (valuationOf q) (231)) (literal (valuationOf q) (233)) (countLit q [117]) (countLit q [118, 119]) (count233 q) 1 (meaning231 q) (meaning233 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 233 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 117 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118, 119])
  have hm := merge_left (literal (valuationOf q) (117)) (literal (valuationOf q) (233)) (countLit q [117]) (countLit q [118, 119]) (count233 q) 1 (meaning117 q) (meaning233 q) hs
  change valuationOf q 117 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 233 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 122 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [121]) + (countLit q [122]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122])
  have hm := merge_right (literal (valuationOf q) (122)) (literal (valuationOf q) (235)) (countLit q [121]) (countLit q [122]) (count235 q) 1 (meaning122 q) (meaning235 q) hs
  change valuationOf q 122 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 235 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121, 122])
  have hm := merge_right (literal (valuationOf q) (235)) (literal (valuationOf q) (237)) (countLit q [120]) (countLit q [121, 122]) (count237 q) 1 (meaning235 q) (meaning237 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 237 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121, 122])
  have hm := merge_left (literal (valuationOf q) (120)) (literal (valuationOf q) (237)) (countLit q [120]) (countLit q [121, 122]) (count237 q) 1 (meaning120 q) (meaning237 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 237 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 235 = false ∨ valuationOf q 238 = true := by
  have hs : count237 q = (countLit q [120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121, 122])
  have hm := merge_two (literal (valuationOf q) (120)) (literal (valuationOf q) (235)) (literal (valuationOf q) (238)) (countLit q [120]) (countLit q [121, 122]) (count237 q) 1 1 (meaning120 q) (meaning235 q) (meaning238 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 235 = false ∨ valuationOf q 238 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 235 = false ∨ valuation q 238 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122])
  have hm := merge_right (literal (valuationOf q) (238)) (literal (valuationOf q) (240)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122]) (count239 q) 2 (meaning238 q) (meaning240 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 240 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E145.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112145
