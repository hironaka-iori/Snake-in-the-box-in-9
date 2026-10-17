import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 228 = false := by
  rw [value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (460 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 231 = false := by
  rw [value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (468 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 234 = false := by
  rw [value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (471 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 235 = false := by
  rw [value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (472 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 237 = false := by
  rw [value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (475 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause582 (q : Nat → Bool) : valuationOf q 122 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [121]) + (countLit q [122]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122])
  have hm := merge_right (literal (valuationOf q) (122)) (literal (valuationOf q) (239)) (countLit q [121]) (countLit q [122]) (count239 q) 1 (meaning122 q) (meaning239 q) hs
  change valuationOf q 122 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 239 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121, 122])
  have hm := merge_right (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (countLit q [120]) (countLit q [121, 122]) (count241 q) 1 (meaning239 q) (meaning241 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121, 122])
  have hm := merge_left (literal (valuationOf q) (120)) (literal (valuationOf q) (241)) (countLit q [120]) (countLit q [121, 122]) (count241 q) 1 (meaning120 q) (meaning241 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 241 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 239 = false ∨ valuationOf q 242 = true := by
  have hs : count241 q = (countLit q [120]) + (countLit q [121, 122]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121, 122])
  have hm := merge_two (literal (valuationOf q) (120)) (literal (valuationOf q) (239)) (literal (valuationOf q) (242)) (countLit q [120]) (countLit q [121, 122]) (count241 q) 1 1 (meaning120 q) (meaning239 q) (meaning242 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 239 = false ∨ valuationOf q 242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 239 = false ∨ valuation q 242 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [120, 121, 122]) + (countLit q [123, 124, 125, 126]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122]) (l₂ := [123, 124, 125, 126])
  have hm := merge_left (literal (valuationOf q) (241)) (literal (valuationOf q) (249)) (countLit q [120, 121, 122]) (countLit q [123, 124, 125, 126]) (count249 q) 1 (meaning241 q) (meaning249 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 249 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 242 = false ∨ valuationOf q 250 = true := by
  have hs : count249 q = (countLit q [120, 121, 122]) + (countLit q [123, 124, 125, 126]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122]) (l₂ := [123, 124, 125, 126])
  have hm := merge_left (literal (valuationOf q) (242)) (literal (valuationOf q) (250)) (countLit q [120, 121, 122]) (countLit q [123, 124, 125, 126]) (count249 q) 2 (meaning242 q) (meaning250 q) hs
  change valuationOf q 242 = false ∨ valuationOf q 250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 250 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_right (literal (valuationOf q) (129)) (literal (valuationOf q) (251)) (countLit q [128]) (countLit q [129]) (count251 q) 1 (meaning129 q) (meaning251 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 251 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (251)) (countLit q [128]) (countLit q [129]) (count251 q) 1 (meaning128 q) (meaning251 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 251 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 129 = false ∨ valuationOf q 252 = true := by
  have hs : count251 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_two (literal (valuationOf q) (128)) (literal (valuationOf q) (129)) (literal (valuationOf q) (252)) (countLit q [128]) (countLit q [129]) (count251 q) 1 1 (meaning128 q) (meaning129 q) (meaning252 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 129 = false ∨ valuationOf q 252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 129 = false ∨ valuation q 252 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128, 129])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [127]) (countLit q [128, 129]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 252 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128, 129])
  have hm := merge_right (literal (valuationOf q) (252)) (literal (valuationOf q) (254)) (countLit q [127]) (countLit q [128, 129]) (count253 q) 2 (meaning252 q) (meaning254 q) hs
  change valuationOf q 252 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 252 = false ∨ valuation q 254 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [130]) + (countLit q [131]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131])
  have hm := merge_right (literal (valuationOf q) (131)) (literal (valuationOf q) (255)) (countLit q [130]) (countLit q [131]) (count255 q) 1 (meaning131 q) (meaning255 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 255 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [130, 131]) + (countLit q [132, 133]) := List.countP_append (p := literal q) (l₁ := [130, 131]) (l₂ := [132, 133])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (259)) (countLit q [130, 131]) (countLit q [132, 133]) (count259 q) 1 (meaning255 q) (meaning259 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 259 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [127, 128, 129]) + (countLit q [130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129]) (l₂ := [130, 131, 132, 133])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [127, 128, 129]) (countLit q [130, 131, 132, 133]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [127, 128, 129]) + (countLit q [130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129]) (l₂ := [130, 131, 132, 133])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (261)) (countLit q [127, 128, 129]) (countLit q [130, 131, 132, 133]) (count261 q) 1 (meaning253 q) (meaning261 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 261 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 259 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [127, 128, 129]) + (countLit q [130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129]) (l₂ := [130, 131, 132, 133])
  have hm := merge_two (literal (valuationOf q) (253)) (literal (valuationOf q) (259)) (literal (valuationOf q) (262)) (countLit q [127, 128, 129]) (countLit q [130, 131, 132, 133]) (count261 q) 1 1 (meaning253 q) (meaning259 q) (meaning262 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 259 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 259 = false ∨ valuation q 262 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 254 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [127, 128, 129]) + (countLit q [130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129]) (l₂ := [130, 131, 132, 133])
  have hm := merge_left (literal (valuationOf q) (254)) (literal (valuationOf q) (262)) (countLit q [127, 128, 129]) (countLit q [130, 131, 132, 133]) (count261 q) 2 (meaning254 q) (meaning262 q) hs
  change valuationOf q 254 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 254 = false ∨ valuation q 262 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [120, 121, 122, 123, 124, 125, 126]) + (countLit q [127, 128, 129, 130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126]) (l₂ := [127, 128, 129, 130, 131, 132, 133])
  have hm := merge_right (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (countLit q [120, 121, 122, 123, 124, 125, 126]) (countLit q [127, 128, 129, 130, 131, 132, 133]) (count263 q) 1 (meaning261 q) (meaning263 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 262 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [120, 121, 122, 123, 124, 125, 126]) + (countLit q [127, 128, 129, 130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126]) (l₂ := [127, 128, 129, 130, 131, 132, 133])
  have hm := merge_right (literal (valuationOf q) (262)) (literal (valuationOf q) (264)) (countLit q [120, 121, 122, 123, 124, 125, 126]) (countLit q [127, 128, 129, 130, 131, 132, 133]) (count263 q) 2 (meaning262 q) (meaning264 q) hs
  change valuationOf q 262 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 262 = false ∨ valuation q 264 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [120, 121, 122, 123, 124, 125, 126]) + (countLit q [127, 128, 129, 130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126]) (l₂ := [127, 128, 129, 130, 131, 132, 133])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (263)) (countLit q [120, 121, 122, 123, 124, 125, 126]) (countLit q [127, 128, 129, 130, 131, 132, 133]) (count263 q) 1 (meaning249 q) (meaning263 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 263 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 261 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [120, 121, 122, 123, 124, 125, 126]) + (countLit q [127, 128, 129, 130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126]) (l₂ := [127, 128, 129, 130, 131, 132, 133])
  have hm := merge_two (literal (valuationOf q) (249)) (literal (valuationOf q) (261)) (literal (valuationOf q) (264)) (countLit q [120, 121, 122, 123, 124, 125, 126]) (countLit q [127, 128, 129, 130, 131, 132, 133]) (count263 q) 1 1 (meaning249 q) (meaning261 q) (meaning264 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 261 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 261 = false ∨ valuation q 264 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 250 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [120, 121, 122, 123, 124, 125, 126]) + (countLit q [127, 128, 129, 130, 131, 132, 133]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126]) (l₂ := [127, 128, 129, 130, 131, 132, 133])
  have hm := merge_left (literal (valuationOf q) (250)) (literal (valuationOf q) (264)) (countLit q [120, 121, 122, 123, 124, 125, 126]) (countLit q [127, 128, 129, 130, 131, 132, 133]) (count263 q) 2 (meaning250 q) (meaning264 q) hs
  change valuationOf q 250 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 250 = false ∨ valuation q 264 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135, 136])
  have hm := merge_left (literal (valuationOf q) (134)) (literal (valuationOf q) (267)) (countLit q [134]) (countLit q [135, 136]) (count267 q) 1 (meaning134 q) (meaning267 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 267 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_right (literal (valuationOf q) (138)) (literal (valuationOf q) (269)) (countLit q [137]) (countLit q [138]) (count269 q) 1 (meaning138 q) (meaning269 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 269 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 137 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_left (literal (valuationOf q) (137)) (literal (valuationOf q) (269)) (countLit q [137]) (countLit q [138]) (count269 q) 1 (meaning137 q) (meaning269 q) hs
  change valuationOf q 137 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 269 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 137 = false ∨ valuationOf q 138 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_two (literal (valuationOf q) (137)) (literal (valuationOf q) (138)) (literal (valuationOf q) (270)) (countLit q [137]) (countLit q [138]) (count269 q) 1 1 (meaning137 q) (meaning138 q) (meaning270 q) hs
  change valuationOf q 137 = false ∨ valuationOf q 138 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 138 = false ∨ valuation q 270 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_right (literal (valuationOf q) (140)) (literal (valuationOf q) (271)) (countLit q [139]) (countLit q [140]) (count271 q) 1 (meaning140 q) (meaning271 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 271 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E078.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112078
