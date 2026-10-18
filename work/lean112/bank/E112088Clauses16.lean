import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 213 = false := by
  rw [value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (443 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 219 = false := by
  rw [value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (487 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 221 = false := by
  rw [value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (491 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 223 = false := by
  rw [value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (493 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 224 = false := by
  rw [value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (496 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 227 = false := by
  rw [value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (502 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 228 = false := by
  rw [value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (505 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause520 (q : Nat → Bool) : valuationOf q 118 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [118]) + (countLit q [119]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119])
  have hm := merge_left (literal (valuationOf q) (118)) (literal (valuationOf q) (233)) (countLit q [118]) (countLit q [119]) (count233 q) 1 (meaning118 q) (meaning233 q) hs
  change valuationOf q 118 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 233 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118, 119])
  have hm := merge_right (literal (valuationOf q) (233)) (literal (valuationOf q) (235)) (countLit q [117]) (countLit q [118, 119]) (count235 q) 1 (meaning233 q) (meaning235 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 235 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 117 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118, 119])
  have hm := merge_left (literal (valuationOf q) (117)) (literal (valuationOf q) (235)) (countLit q [117]) (countLit q [118, 119]) (count235 q) 1 (meaning117 q) (meaning235 q) hs
  change valuationOf q 117 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 235 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 117 = false ∨ valuationOf q 233 = false ∨ valuationOf q 236 = true := by
  have hs : count235 q = (countLit q [117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118, 119])
  have hm := merge_two (literal (valuationOf q) (117)) (literal (valuationOf q) (233)) (literal (valuationOf q) (236)) (countLit q [117]) (countLit q [118, 119]) (count235 q) 1 1 (meaning117 q) (meaning233 q) (meaning236 q) hs
  change valuationOf q 117 = false ∨ valuationOf q 233 = false ∨ valuationOf q 236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 233 = false ∨ valuation q 236 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [120]) + (countLit q [121]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121])
  have hm := merge_left (literal (valuationOf q) (120)) (literal (valuationOf q) (237)) (countLit q [120]) (countLit q [121]) (count237 q) 1 (meaning120 q) (meaning237 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 237 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 123 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [122]) + (countLit q [123]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123])
  have hm := merge_right (literal (valuationOf q) (123)) (literal (valuationOf q) (239)) (countLit q [122]) (countLit q [123]) (count239 q) 1 (meaning123 q) (meaning239 q) hs
  change valuationOf q 123 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 239 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [120, 121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [120, 121]) (l₂ := [122, 123])
  have hm := merge_right (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (countLit q [120, 121]) (countLit q [122, 123]) (count241 q) 1 (meaning239 q) (meaning241 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [120, 121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [120, 121]) (l₂ := [122, 123])
  have hm := merge_left (literal (valuationOf q) (237)) (literal (valuationOf q) (241)) (countLit q [120, 121]) (countLit q [122, 123]) (count241 q) 1 (meaning237 q) (meaning241 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 241 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (243)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count243 q) 1 (meaning235 q) (meaning243 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 243 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 241 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_two (literal (valuationOf q) (235)) (literal (valuationOf q) (241)) (literal (valuationOf q) (244)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count243 q) 1 1 (meaning235 q) (meaning241 q) (meaning244 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 241 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 241 = false ∨ valuation q 244 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 236 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (236)) (literal (valuationOf q) (244)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count243 q) 2 (meaning236 q) (meaning244 q) hs
  change valuationOf q 236 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 244 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 127 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127])
  have hm := merge_right (literal (valuationOf q) (127)) (literal (valuationOf q) (245)) (countLit q [126]) (countLit q [127]) (count245 q) 1 (meaning127 q) (meaning245 q) hs
  change valuationOf q 127 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 245 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 126 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127])
  have hm := merge_left (literal (valuationOf q) (126)) (literal (valuationOf q) (245)) (countLit q [126]) (countLit q [127]) (count245 q) 1 (meaning126 q) (meaning245 q) hs
  change valuationOf q 126 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 245 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [125]) + (countLit q [126, 127]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126, 127])
  have hm := merge_right (literal (valuationOf q) (245)) (literal (valuationOf q) (247)) (countLit q [125]) (countLit q [126, 127]) (count247 q) 1 (meaning245 q) (meaning247 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 247 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (249)) (countLit q [128]) (countLit q [129]) (count249 q) 1 (meaning128 q) (meaning249 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 249 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [130]) + (countLit q [131]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131])
  have hm := merge_right (literal (valuationOf q) (131)) (literal (valuationOf q) (251)) (countLit q [130]) (countLit q [131]) (count251 q) 1 (meaning131 q) (meaning251 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 251 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 130 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [130]) + (countLit q [131]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131])
  have hm := merge_left (literal (valuationOf q) (130)) (literal (valuationOf q) (251)) (countLit q [130]) (countLit q [131]) (count251 q) 1 (meaning130 q) (meaning251 q) hs
  change valuationOf q 130 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 251 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [128, 129]) (countLit q [130, 131]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (253)) (countLit q [128, 129]) (countLit q [130, 131]) (count253 q) 1 (meaning249 q) (meaning253 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 253 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_two (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (literal (valuationOf q) (254)) (countLit q [128, 129]) (countLit q [130, 131]) (count253 q) 1 1 (meaning249 q) (meaning251 q) (meaning254 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = false ∨ valuation q 254 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 254 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (254)) (literal (valuationOf q) (256)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count255 q) 2 (meaning254 q) (meaning256 q) hs
  change valuationOf q 254 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 254 = false ∨ valuation q 256 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (255)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count255 q) 1 (meaning247 q) (meaning255 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 255 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [117, 118, 119, 120, 121, 122, 123]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [117, 118, 119, 120, 121, 122, 123]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E088.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112088
