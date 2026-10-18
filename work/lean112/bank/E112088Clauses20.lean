import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_right (literal (valuationOf q) (395)) (literal (valuationOf q) (397)) (countLit q [189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) (count397 q) 1 (meaning395 q) (meaning397 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 397 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_right (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 1 (meaning397 q) (meaning399 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_left (literal (valuationOf q) (369)) (literal (valuationOf q) (399)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 1 (meaning369 q) (meaning399 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 399 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 397 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_two (literal (valuationOf q) (369)) (literal (valuationOf q) (397)) (literal (valuationOf q) (400)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 1 1 (meaning369 q) (meaning397 q) (meaning400 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 397 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 397 = false ∨ valuation q 400 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 370 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_left (literal (valuationOf q) (370)) (literal (valuationOf q) (400)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 2 (meaning370 q) (meaning400 q) hs
  change valuationOf q 370 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 370 = false ∨ valuation q 400 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 205 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [205]) + (countLit q [206]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206])
  have hm := merge_left (literal (valuationOf q) (205)) (literal (valuationOf q) (401)) (countLit q [205]) (countLit q [206]) (count401 q) 1 (meaning205 q) (meaning401 q) hs
  change valuationOf q 205 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 401 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [204]) + (countLit q [205, 206]) := List.countP_append (p := literal q) (l₁ := [204]) (l₂ := [205, 206])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [204]) (countLit q [205, 206]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_left (literal (valuationOf q) (209)) (literal (valuationOf q) (407)) (countLit q [209]) (countLit q [210]) (count407 q) 1 (meaning209 q) (meaning407 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 407 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [207, 208]) + (countLit q [209, 210]) := List.countP_append (p := literal q) (l₁ := [207, 208]) (l₂ := [209, 210])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [207, 208]) (countLit q [209, 210]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [204, 205, 206]) + (countLit q [207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206]) (l₂ := [207, 208, 209, 210])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [204, 205, 206]) (countLit q [207, 208, 209, 210]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [204, 205, 206]) + (countLit q [207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206]) (l₂ := [207, 208, 209, 210])
  have hm := merge_left (literal (valuationOf q) (403)) (literal (valuationOf q) (411)) (countLit q [204, 205, 206]) (countLit q [207, 208, 209, 210]) (count411 q) 1 (meaning403 q) (meaning411 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 411 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_left (literal (valuationOf q) (212)) (literal (valuationOf q) (413)) (countLit q [212]) (countLit q [213]) (count413 q) 1 (meaning212 q) (meaning413 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 413 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [211]) + (countLit q [212, 213]) := List.countP_append (p := literal q) (l₁ := [211]) (l₂ := [212, 213])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [211]) (countLit q [212, 213]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [216]) + (countLit q [217]) := List.countP_append (p := literal q) (l₁ := [216]) (l₂ := [217])
  have hm := merge_right (literal (valuationOf q) (217)) (literal (valuationOf q) (419)) (countLit q [216]) (countLit q [217]) (count419 q) 1 (meaning217 q) (meaning419 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 419 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_right (literal (valuationOf q) (419)) (literal (valuationOf q) (421)) (countLit q [214, 215]) (countLit q [216, 217]) (count421 q) 1 (meaning419 q) (meaning421 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 421 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (421)) (literal (valuationOf q) (423)) (countLit q [211, 212, 213]) (countLit q [214, 215, 216, 217]) (count423 q) 1 (meaning421 q) (meaning423 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (415)) (literal (valuationOf q) (423)) (countLit q [211, 212, 213]) (countLit q [214, 215, 216, 217]) (count423 q) 1 (meaning415 q) (meaning423 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 423 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [204, 205, 206, 207, 208, 209, 210]) + (countLit q [211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210]) (l₂ := [211, 212, 213, 214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [204, 205, 206, 207, 208, 209, 210]) (countLit q [211, 212, 213, 214, 215, 216, 217]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [204, 205, 206, 207, 208, 209, 210]) + (countLit q [211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210]) (l₂ := [211, 212, 213, 214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (411)) (literal (valuationOf q) (425)) (countLit q [204, 205, 206, 207, 208, 209, 210]) (countLit q [211, 212, 213, 214, 215, 216, 217]) (count425 q) 1 (meaning411 q) (meaning425 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 425 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 423 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [204, 205, 206, 207, 208, 209, 210]) + (countLit q [211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210]) (l₂ := [211, 212, 213, 214, 215, 216, 217])
  have hm := merge_two (literal (valuationOf q) (411)) (literal (valuationOf q) (423)) (literal (valuationOf q) (426)) (countLit q [204, 205, 206, 207, 208, 209, 210]) (countLit q [211, 212, 213, 214, 215, 216, 217]) (count425 q) 1 1 (meaning411 q) (meaning423 q) (meaning426 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 423 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 423 = false ∨ valuation q 426 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 220 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [219]) + (countLit q [220]) := List.countP_append (p := literal q) (l₁ := [219]) (l₂ := [220])
  have hm := merge_right (literal (valuationOf q) (220)) (literal (valuationOf q) (427)) (countLit q [219]) (countLit q [220]) (count427 q) 1 (meaning220 q) (meaning427 q) hs
  change valuationOf q 220 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 427 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [218]) (l₂ := [219, 220])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [218]) (countLit q [219, 220]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 218 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [218]) (l₂ := [219, 220])
  have hm := merge_left (literal (valuationOf q) (218)) (literal (valuationOf q) (429)) (countLit q [218]) (countLit q [219, 220]) (count429 q) 1 (meaning218 q) (meaning429 q) hs
  change valuationOf q 218 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 429 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [218, 219, 220]) + (countLit q [221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220]) (l₂ := [221, 222, 223, 224])
  have hm := merge_left (literal (valuationOf q) (429)) (literal (valuationOf q) (437)) (countLit q [218, 219, 220]) (countLit q [221, 222, 223, 224]) (count437 q) 1 (meaning429 q) (meaning437 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 437 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_left (literal (valuationOf q) (225)) (literal (valuationOf q) (439)) (countLit q [225]) (countLit q [226]) (count439 q) 1 (meaning225 q) (meaning439 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 439 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_left (literal (valuationOf q) (439)) (literal (valuationOf q) (443)) (countLit q [225, 226]) (countLit q [227, 228]) (count443 q) 1 (meaning439 q) (meaning443 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 443 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [225, 226, 227, 228]) + (countLit q [229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228]) (l₂ := [229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (443)) (literal (valuationOf q) (451)) (countLit q [225, 226, 227, 228]) (countLit q [229, 230, 231, 232]) (count451 q) 1 (meaning443 q) (meaning451 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 451 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (451)) (literal (valuationOf q) (453)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count453 q) 1 (meaning451 q) (meaning453 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 453 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (453)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count453 q) 1 (meaning437 q) (meaning453 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 453 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (455)) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 (meaning425 q) (meaning455 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 455 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (425)) (literal (valuationOf q) (453)) (literal (valuationOf q) (456)) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 1 (meaning425 q) (meaning453 q) (meaning456 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 453 = false ∨ valuation q 456 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E088.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112088
