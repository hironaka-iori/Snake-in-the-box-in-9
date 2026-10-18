import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118, 119])
  have hm := merge_right (literal (valuationOf q) (233)) (literal (valuationOf q) (235)) (countLit q [117]) (countLit q [118, 119]) (count235 q) 1 (meaning233 q) (meaning235 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 235 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [120]) + (countLit q [121]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121])
  have hm := merge_left (literal (valuationOf q) (120)) (literal (valuationOf q) (237)) (countLit q [120]) (countLit q [121]) (count237 q) 1 (meaning120 q) (meaning237 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 237 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 120 = false ∨ valuationOf q 121 = false ∨ valuationOf q 238 = true := by
  have hs : count237 q = (countLit q [120]) + (countLit q [121]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121])
  have hm := merge_two (literal (valuationOf q) (120)) (literal (valuationOf q) (121)) (literal (valuationOf q) (238)) (countLit q [120]) (countLit q [121]) (count237 q) 1 1 (meaning120 q) (meaning121 q) (meaning238 q) hs
  change valuationOf q 120 = false ∨ valuationOf q 121 = false ∨ valuationOf q 238 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 121 = false ∨ valuation q 238 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [120, 121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [120, 121]) (l₂ := [122, 123])
  have hm := merge_left (literal (valuationOf q) (237)) (literal (valuationOf q) (241)) (countLit q [120, 121]) (countLit q [122, 123]) (count241 q) 1 (meaning237 q) (meaning241 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 241 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 242 = true := by
  have hs : count241 q = (countLit q [120, 121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [120, 121]) (l₂ := [122, 123])
  have hm := merge_left (literal (valuationOf q) (238)) (literal (valuationOf q) (242)) (countLit q [120, 121]) (countLit q [122, 123]) (count241 q) 2 (meaning238 q) (meaning242 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 242 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 242 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (242)) (literal (valuationOf q) (244)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count243 q) 2 (meaning242 q) (meaning244 q) hs
  change valuationOf q 242 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 244 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (243)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count243 q) 1 (meaning235 q) (meaning243 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 243 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 241 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_two (literal (valuationOf q) (235)) (literal (valuationOf q) (241)) (literal (valuationOf q) (244)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count243 q) 1 1 (meaning235 q) (meaning241 q) (meaning244 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 241 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 241 = false ∨ valuation q 244 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 125 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [125]) + (countLit q [126]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126])
  have hm := merge_left (literal (valuationOf q) (125)) (literal (valuationOf q) (245)) (countLit q [125]) (countLit q [126]) (count245 q) 1 (meaning125 q) (meaning245 q) hs
  change valuationOf q 125 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 245 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [124]) + (countLit q [125, 126]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125, 126])
  have hm := merge_right (literal (valuationOf q) (245)) (literal (valuationOf q) (247)) (countLit q [124]) (countLit q [125, 126]) (count247 q) 1 (meaning245 q) (meaning247 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 247 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [124]) + (countLit q [125, 126]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125, 126])
  have hm := merge_left (literal (valuationOf q) (124)) (literal (valuationOf q) (247)) (countLit q [124]) (countLit q [125, 126]) (count247 q) 1 (meaning124 q) (meaning247 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 247 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 245 = false ∨ valuationOf q 248 = true := by
  have hs : count247 q = (countLit q [124]) + (countLit q [125, 126]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125, 126])
  have hm := merge_two (literal (valuationOf q) (124)) (literal (valuationOf q) (245)) (literal (valuationOf q) (248)) (countLit q [124]) (countLit q [125, 126]) (count247 q) 1 1 (meaning124 q) (meaning245 q) (meaning248 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 245 = false ∨ valuationOf q 248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 245 = false ∨ valuation q 248 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [127]) + (countLit q [128]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128])
  have hm := merge_right (literal (valuationOf q) (128)) (literal (valuationOf q) (249)) (countLit q [127]) (countLit q [128]) (count249 q) 1 (meaning128 q) (meaning249 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 249 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_left (literal (valuationOf q) (129)) (literal (valuationOf q) (251)) (countLit q [129]) (countLit q [130]) (count251 q) 1 (meaning129 q) (meaning251 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 251 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [127, 128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [127, 128]) (l₂ := [129, 130])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [127, 128]) (countLit q [129, 130]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [127, 128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [127, 128]) (l₂ := [129, 130])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (253)) (countLit q [127, 128]) (countLit q [129, 130]) (count253 q) 1 (meaning249 q) (meaning253 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 253 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [127, 128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [127, 128]) (l₂ := [129, 130])
  have hm := merge_two (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (literal (valuationOf q) (254)) (countLit q [127, 128]) (countLit q [129, 130]) (count253 q) 1 1 (meaning249 q) (meaning251 q) (meaning254 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = false ∨ valuation q 254 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 254 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_right (literal (valuationOf q) (254)) (literal (valuationOf q) (256)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count255 q) 2 (meaning254 q) (meaning256 q) hs
  change valuationOf q 254 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 254 = false ∨ valuation q 256 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (255)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count255 q) 1 (meaning247 q) (meaning255 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 255 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_two (literal (valuationOf q) (247)) (literal (valuationOf q) (253)) (literal (valuationOf q) (256)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count255 q) 1 1 (meaning247 q) (meaning253 q) (meaning256 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 253 = false ∨ valuation q 256 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 248 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_left (literal (valuationOf q) (248)) (literal (valuationOf q) (256)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count255 q) 2 (meaning248 q) (meaning256 q) hs
  change valuationOf q 248 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 256 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 256 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130])
  have hm := merge_right (literal (valuationOf q) (256)) (literal (valuationOf q) (258)) (countLit q [117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130]) (count257 q) 2 (meaning256 q) (meaning258 q) hs
  change valuationOf q 256 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 256 = false ∨ valuation q 258 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (257)) (countLit q [117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130]) (count257 q) 1 (meaning243 q) (meaning257 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 257 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130])
  have hm := merge_two (literal (valuationOf q) (243)) (literal (valuationOf q) (255)) (literal (valuationOf q) (258)) (countLit q [117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130]) (count257 q) 1 1 (meaning243 q) (meaning255 q) (meaning258 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 255 = false ∨ valuation q 258 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130])
  have hm := merge_left (literal (valuationOf q) (244)) (literal (valuationOf q) (258)) (countLit q [117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130]) (count257 q) 2 (meaning244 q) (meaning258 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 258 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_left (literal (valuationOf q) (132)) (literal (valuationOf q) (259)) (countLit q [132]) (countLit q [133]) (count259 q) 1 (meaning132 q) (meaning259 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 259 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [131]) + (countLit q [132, 133]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132, 133])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [131]) (countLit q [132, 133]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135])
  have hm := merge_left (literal (valuationOf q) (134)) (literal (valuationOf q) (263)) (countLit q [134]) (countLit q [135]) (count263 q) 1 (meaning134 q) (meaning263 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 263 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [136]) + (countLit q [137]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137])
  have hm := merge_left (literal (valuationOf q) (136)) (literal (valuationOf q) (265)) (countLit q [136]) (countLit q [137]) (count265 q) 1 (meaning136 q) (meaning265 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 265 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E259.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112259
