import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 228 = false := by
  rw [value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (464 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 230 = false := by
  rw [value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (469 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 231 = false := by
  rw [value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (470 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 234 = false := by
  rw [value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (473 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 236 = false := by
  rw [value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (479 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause678 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [120]) + (countLit q [121]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121])
  have hm := merge_right (literal (valuationOf q) (121)) (literal (valuationOf q) (237)) (countLit q [120]) (countLit q [121]) (count237 q) 1 (meaning121 q) (meaning237 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 237 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [120]) + (countLit q [121]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121])
  have hm := merge_left (literal (valuationOf q) (120)) (literal (valuationOf q) (237)) (countLit q [120]) (countLit q [121]) (count237 q) 1 (meaning120 q) (meaning237 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 237 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 121 = false ∨ valuationOf q 238 = true := by
  have hs : count237 q = (countLit q [120]) + (countLit q [121]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121])
  have hm := merge_two (literal (valuationOf q) (120)) (literal (valuationOf q) (121)) (literal (valuationOf q) (238)) (countLit q [120]) (countLit q [121]) (count237 q) 1 1 (meaning120 q) (meaning121 q) (meaning238 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 121 = false ∨ valuationOf q 238 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 121 = false ∨ valuation q 238 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [119]) + (countLit q [120, 121]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120, 121])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [119]) (countLit q [120, 121]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [119]) + (countLit q [120, 121]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120, 121])
  have hm := merge_right (literal (valuationOf q) (238)) (literal (valuationOf q) (240)) (countLit q [119]) (countLit q [120, 121]) (count239 q) 2 (meaning238 q) (meaning240 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 240 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 125 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [124]) + (countLit q [125]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125])
  have hm := merge_right (literal (valuationOf q) (125)) (literal (valuationOf q) (243)) (countLit q [124]) (countLit q [125]) (count243 q) 1 (meaning125 q) (meaning243 q) hs
  change valuationOf q 125 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 243 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [122, 123]) + (countLit q [124, 125]) := List.countP_append (p := literal q) (l₁ := [122, 123]) (l₂ := [124, 125])
  have hm := merge_right (literal (valuationOf q) (243)) (literal (valuationOf q) (245)) (countLit q [122, 123]) (countLit q [124, 125]) (count245 q) 1 (meaning243 q) (meaning245 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 245 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [119, 120, 121]) + (countLit q [122, 123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121]) (l₂ := [122, 123, 124, 125])
  have hm := merge_right (literal (valuationOf q) (245)) (literal (valuationOf q) (247)) (countLit q [119, 120, 121]) (countLit q [122, 123, 124, 125]) (count247 q) 1 (meaning245 q) (meaning247 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 247 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [119, 120, 121]) + (countLit q [122, 123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121]) (l₂ := [122, 123, 124, 125])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (247)) (countLit q [119, 120, 121]) (countLit q [122, 123, 124, 125]) (count247 q) 1 (meaning239 q) (meaning247 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 247 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 245 = false ∨ valuationOf q 248 = true := by
  have hs : count247 q = (countLit q [119, 120, 121]) + (countLit q [122, 123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121]) (l₂ := [122, 123, 124, 125])
  have hm := merge_two (literal (valuationOf q) (239)) (literal (valuationOf q) (245)) (literal (valuationOf q) (248)) (countLit q [119, 120, 121]) (countLit q [122, 123, 124, 125]) (count247 q) 1 1 (meaning239 q) (meaning245 q) (meaning248 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 245 = false ∨ valuationOf q 248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 245 = false ∨ valuation q 248 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 240 = false ∨ valuationOf q 248 = true := by
  have hs : count247 q = (countLit q [119, 120, 121]) + (countLit q [122, 123, 124, 125]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121]) (l₂ := [122, 123, 124, 125])
  have hm := merge_left (literal (valuationOf q) (240)) (literal (valuationOf q) (248)) (countLit q [119, 120, 121]) (countLit q [122, 123, 124, 125]) (count247 q) 2 (meaning240 q) (meaning248 q) hs
  change valuationOf q 240 = false ∨ valuationOf q 248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 248 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 126 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [126]) + (countLit q [127, 128]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127, 128])
  have hm := merge_left (literal (valuationOf q) (126)) (literal (valuationOf q) (251)) (countLit q [126]) (countLit q [127, 128]) (count251 q) 1 (meaning126 q) (meaning251 q) hs
  change valuationOf q 126 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 251 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_left (literal (valuationOf q) (129)) (literal (valuationOf q) (253)) (countLit q [129]) (countLit q [130]) (count253 q) 1 (meaning129 q) (meaning253 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 253 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_left (literal (valuationOf q) (131)) (literal (valuationOf q) (255)) (countLit q [131]) (countLit q [132]) (count255 q) 1 (meaning131 q) (meaning255 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 255 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [129, 130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [129, 130]) (l₂ := [131, 132])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [129, 130]) (countLit q [131, 132]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [129, 130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [129, 130]) (l₂ := [131, 132])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (257)) (countLit q [129, 130]) (countLit q [131, 132]) (count257 q) 1 (meaning253 q) (meaning257 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 257 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (259)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count259 q) 1 (meaning251 q) (meaning259 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 259 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_two (literal (valuationOf q) (251)) (literal (valuationOf q) (257)) (literal (valuationOf q) (260)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count259 q) 1 1 (meaning251 q) (meaning257 q) (meaning260 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 257 = false ∨ valuation q 260 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 260 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (260)) (literal (valuationOf q) (262)) (countLit q [119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count261 q) 2 (meaning260 q) (meaning262 q) hs
  change valuationOf q 260 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 260 = false ∨ valuation q 262 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (261)) (countLit q [119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count261 q) 1 (meaning247 q) (meaning261 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 261 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 259 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_two (literal (valuationOf q) (247)) (literal (valuationOf q) (259)) (literal (valuationOf q) (262)) (countLit q [119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count261 q) 1 1 (meaning247 q) (meaning259 q) (meaning262 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 259 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 259 = false ∨ valuation q 262 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 248 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (248)) (literal (valuationOf q) (262)) (countLit q [119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count261 q) 2 (meaning248 q) (meaning262 q) hs
  change valuationOf q 248 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 262 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135])
  have hm := merge_right (literal (valuationOf q) (135)) (literal (valuationOf q) (263)) (countLit q [134]) (countLit q [135]) (count263 q) 1 (meaning135 q) (meaning263 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 263 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [133]) (countLit q [134, 135]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_left (literal (valuationOf q) (133)) (literal (valuationOf q) (265)) (countLit q [133]) (countLit q [134, 135]) (count265 q) 1 (meaning133 q) (meaning265 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 265 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E027.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112027
