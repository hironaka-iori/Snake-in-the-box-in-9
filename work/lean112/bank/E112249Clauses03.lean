import E112249Semantics
import B112E249Inputs
namespace Snake9.Regrowth.E112249
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 145 = false := by
  rw [value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (175 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 149 = false := by
  rw [value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (189 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 150 = false := by
  rw [value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (190 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 161 = false := by
  rw [value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (277 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 181 = false := by
  rw [value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (366 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 182 = false := by
  rw [value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (418 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 191 = false := by
  rw [value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (437 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 197 = false := by
  rw [value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (480 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause105 (q : Nat → Bool) : valuationOf q 108 = false ∨ valuationOf q 213 = true := by
  have hs : count213 q = (countLit q [108]) + (countLit q [109]) := List.countP_append (p := literal q) (l₁ := [108]) (l₂ := [109])
  have hm := merge_left (literal (valuationOf q) (108)) (literal (valuationOf q) (213)) (countLit q [108]) (countLit q [109]) (count213 q) 1 (meaning108 q) (meaning213 q) hs
  change valuationOf q 108 = false ∨ valuationOf q 213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 213 = true := counterClause105 (baseVal q)

theorem counterClause106 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 215 = true := by
  have hs : count215 q = (countLit q [107]) + (countLit q [108, 109]) := List.countP_append (p := literal q) (l₁ := [107]) (l₂ := [108, 109])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (215)) (countLit q [107]) (countLit q [108, 109]) (count215 q) 1 (meaning213 q) (meaning215 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 215 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 215 = true := counterClause106 (baseVal q)

theorem counterClause107 (q : Nat → Bool) : valuationOf q 111 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [111]) + (countLit q [112]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112])
  have hm := merge_left (literal (valuationOf q) (111)) (literal (valuationOf q) (217)) (countLit q [111]) (countLit q [112]) (count217 q) 1 (meaning111 q) (meaning217 q) hs
  change valuationOf q 111 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 217 = true := counterClause107 (baseVal q)

theorem counterClause108 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [110]) + (countLit q [111, 112]) := List.countP_append (p := literal q) (l₁ := [110]) (l₂ := [111, 112])
  have hm := merge_right (literal (valuationOf q) (217)) (literal (valuationOf q) (219)) (countLit q [110]) (countLit q [111, 112]) (count219 q) 1 (meaning217 q) (meaning219 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 219 = true := counterClause108 (baseVal q)

theorem counterClause109 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [107, 108, 109]) + (countLit q [110, 111, 112]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109]) (l₂ := [110, 111, 112])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (221)) (countLit q [107, 108, 109]) (countLit q [110, 111, 112]) (count221 q) 1 (meaning219 q) (meaning221 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 221 = true := counterClause109 (baseVal q)

theorem counterClause110 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [107, 108, 109]) + (countLit q [110, 111, 112]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109]) (l₂ := [110, 111, 112])
  have hm := merge_left (literal (valuationOf q) (215)) (literal (valuationOf q) (221)) (countLit q [107, 108, 109]) (countLit q [110, 111, 112]) (count221 q) 1 (meaning215 q) (meaning221 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 221 = true := counterClause110 (baseVal q)

theorem counterClause111 (q : Nat → Bool) : valuationOf q 117 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [116]) + (countLit q [117]) := List.countP_append (p := literal q) (l₁ := [116]) (l₂ := [117])
  have hm := merge_right (literal (valuationOf q) (117)) (literal (valuationOf q) (227)) (countLit q [116]) (countLit q [117]) (count227 q) 1 (meaning117 q) (meaning227 q) hs
  change valuationOf q 117 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 227 = true := counterClause111 (baseVal q)

theorem counterClause112 (q : Nat → Bool) : valuationOf q 118 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [118]) + (countLit q [119]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119])
  have hm := merge_left (literal (valuationOf q) (118)) (literal (valuationOf q) (229)) (countLit q [118]) (countLit q [119]) (count229 q) 1 (meaning118 q) (meaning229 q) hs
  change valuationOf q 118 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 229 = true := counterClause112 (baseVal q)

theorem counterClause113 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [116, 117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [116, 117]) (l₂ := [118, 119])
  have hm := merge_left (literal (valuationOf q) (227)) (literal (valuationOf q) (231)) (countLit q [116, 117]) (countLit q [118, 119]) (count231 q) 1 (meaning227 q) (meaning231 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 231 = true := counterClause113 (baseVal q)

theorem counterClause114 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 229 = false ∨ valuationOf q 232 = true := by
  have hs : count231 q = (countLit q [116, 117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [116, 117]) (l₂ := [118, 119])
  have hm := merge_two (literal (valuationOf q) (227)) (literal (valuationOf q) (229)) (literal (valuationOf q) (232)) (countLit q [116, 117]) (countLit q [118, 119]) (count231 q) 1 1 (meaning227 q) (meaning229 q) (meaning232 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 229 = false ∨ valuationOf q 232 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 229 = false ∨ valuation q 232 = true := counterClause114 (baseVal q)

theorem counterClause115 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [113, 114, 115]) + (countLit q [116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [113, 114, 115]) (l₂ := [116, 117, 118, 119])
  have hm := merge_right (literal (valuationOf q) (231)) (literal (valuationOf q) (233)) (countLit q [113, 114, 115]) (countLit q [116, 117, 118, 119]) (count233 q) 1 (meaning231 q) (meaning233 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 233 = true := counterClause115 (baseVal q)

theorem counterClause116 (q : Nat → Bool) : valuationOf q 232 = false ∨ valuationOf q 234 = true := by
  have hs : count233 q = (countLit q [113, 114, 115]) + (countLit q [116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [113, 114, 115]) (l₂ := [116, 117, 118, 119])
  have hm := merge_right (literal (valuationOf q) (232)) (literal (valuationOf q) (234)) (countLit q [113, 114, 115]) (countLit q [116, 117, 118, 119]) (count233 q) 2 (meaning232 q) (meaning234 q) hs
  change valuationOf q 232 = false ∨ valuationOf q 234 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 234 = true := counterClause116 (baseVal q)

theorem counterClause117 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [107, 108, 109, 110, 111, 112]) + (countLit q [113, 114, 115, 116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112]) (l₂ := [113, 114, 115, 116, 117, 118, 119])
  have hm := merge_right (literal (valuationOf q) (233)) (literal (valuationOf q) (235)) (countLit q [107, 108, 109, 110, 111, 112]) (countLit q [113, 114, 115, 116, 117, 118, 119]) (count235 q) 1 (meaning233 q) (meaning235 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 235 = true := counterClause117 (baseVal q)

theorem counterClause118 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 236 = true := by
  have hs : count235 q = (countLit q [107, 108, 109, 110, 111, 112]) + (countLit q [113, 114, 115, 116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112]) (l₂ := [113, 114, 115, 116, 117, 118, 119])
  have hm := merge_right (literal (valuationOf q) (234)) (literal (valuationOf q) (236)) (countLit q [107, 108, 109, 110, 111, 112]) (countLit q [113, 114, 115, 116, 117, 118, 119]) (count235 q) 2 (meaning234 q) (meaning236 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 236 = true := counterClause118 (baseVal q)

theorem counterClause119 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [107, 108, 109, 110, 111, 112]) + (countLit q [113, 114, 115, 116, 117, 118, 119]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112]) (l₂ := [113, 114, 115, 116, 117, 118, 119])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (235)) (countLit q [107, 108, 109, 110, 111, 112]) (countLit q [113, 114, 115, 116, 117, 118, 119]) (count235 q) 1 (meaning221 q) (meaning235 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 235 = true := counterClause119 (baseVal q)

theorem counterClause120 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121, 122])
  have hm := merge_left (literal (valuationOf q) (120)) (literal (valuationOf q) (239)) (countLit q [120]) (countLit q [121, 122]) (count239 q) 1 (meaning120 q) (meaning239 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 239 = true := counterClause120 (baseVal q)

theorem counterClause121 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [120, 121, 122]) + (countLit q [123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122]) (l₂ := [123, 124, 125])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (245)) (countLit q [120, 121, 122]) (countLit q [123, 124, 125]) (count245 q) 1 (meaning239 q) (meaning245 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 245 = true := counterClause121 (baseVal q)

theorem counterClause122 (q : Nat → Bool) : valuationOf q 127 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [127]) + (countLit q [128]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128])
  have hm := merge_left (literal (valuationOf q) (127)) (literal (valuationOf q) (247)) (countLit q [127]) (countLit q [128]) (count247 q) 1 (meaning127 q) (meaning247 q) hs
  change valuationOf q 127 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 247 = true := counterClause122 (baseVal q)

theorem counterClause123 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [126]) + (countLit q [127, 128]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127, 128])
  have hm := merge_right (literal (valuationOf q) (247)) (literal (valuationOf q) (249)) (countLit q [126]) (countLit q [127, 128]) (count249 q) 1 (meaning247 q) (meaning249 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 249 = true := counterClause123 (baseVal q)

theorem counterClause124 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (257)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count257 q) 1 (meaning249 q) (meaning257 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 257 = true := counterClause124 (baseVal q)

theorem counterClause125 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause125 (baseVal q)

theorem counterClause126 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (259)) (countLit q [120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count259 q) 1 (meaning245 q) (meaning259 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 259 = true := counterClause126 (baseVal q)

theorem counterClause127 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) + (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (l₂ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause127 (baseVal q)

theorem counterClause128 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) + (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (l₂ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (261)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (count261 q) 1 (meaning235 q) (meaning261 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 261 = true := counterClause128 (baseVal q)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E249.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112249
