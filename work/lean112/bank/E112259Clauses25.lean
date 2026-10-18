import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 397 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_two (literal (valuationOf q) (369)) (literal (valuationOf q) (397)) (literal (valuationOf q) (400)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 1 1 (meaning369 q) (meaning397 q) (meaning400 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 397 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 397 = false ∨ valuation q 400 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 370 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_left (literal (valuationOf q) (370)) (literal (valuationOf q) (400)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 2 (meaning370 q) (meaning400 q) hs
  change valuationOf q 370 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 370 = false ∨ valuation q 400 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [207]) + (countLit q [208]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208])
  have hm := merge_right (literal (valuationOf q) (208)) (literal (valuationOf q) (405)) (countLit q [207]) (countLit q [208]) (count405 q) 1 (meaning208 q) (meaning405 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 405 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_left (literal (valuationOf q) (209)) (literal (valuationOf q) (407)) (countLit q [209]) (countLit q [210]) (count407 q) 1 (meaning209 q) (meaning407 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 407 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [207, 208]) + (countLit q [209, 210]) := List.countP_append (p := literal q) (l₁ := [207, 208]) (l₂ := [209, 210])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [207, 208]) (countLit q [209, 210]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [207, 208]) + (countLit q [209, 210]) := List.countP_append (p := literal q) (l₁ := [207, 208]) (l₂ := [209, 210])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (409)) (countLit q [207, 208]) (countLit q [209, 210]) (count409 q) 1 (meaning405 q) (meaning409 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 409 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [204, 205, 206]) + (countLit q [207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206]) (l₂ := [207, 208, 209, 210])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [204, 205, 206]) (countLit q [207, 208, 209, 210]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_left (literal (valuationOf q) (212)) (literal (valuationOf q) (413)) (countLit q [212]) (countLit q [213]) (count413 q) 1 (meaning212 q) (meaning413 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 413 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [211]) + (countLit q [212, 213]) := List.countP_append (p := literal q) (l₁ := [211]) (l₂ := [212, 213])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [211]) (countLit q [212, 213]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 214 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_left (literal (valuationOf q) (214)) (literal (valuationOf q) (417)) (countLit q [214]) (countLit q [215]) (count417 q) 1 (meaning214 q) (meaning417 q) hs
  change valuationOf q 214 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 417 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (421)) (countLit q [214, 215]) (countLit q [216, 217]) (count421 q) 1 (meaning417 q) (meaning421 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 421 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (421)) (literal (valuationOf q) (423)) (countLit q [211, 212, 213]) (countLit q [214, 215, 216, 217]) (count423 q) 1 (meaning421 q) (meaning423 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (415)) (literal (valuationOf q) (423)) (countLit q [211, 212, 213]) (countLit q [214, 215, 216, 217]) (count423 q) 1 (meaning415 q) (meaning423 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 423 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [204, 205, 206, 207, 208, 209, 210]) + (countLit q [211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210]) (l₂ := [211, 212, 213, 214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [204, 205, 206, 207, 208, 209, 210]) (countLit q [211, 212, 213, 214, 215, 216, 217]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [204, 205, 206, 207, 208, 209, 210]) + (countLit q [211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210]) (l₂ := [211, 212, 213, 214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (411)) (literal (valuationOf q) (425)) (countLit q [204, 205, 206, 207, 208, 209, 210]) (countLit q [211, 212, 213, 214, 215, 216, 217]) (count425 q) 1 (meaning411 q) (meaning425 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 425 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [219]) + (countLit q [220]) := List.countP_append (p := literal q) (l₁ := [219]) (l₂ := [220])
  have hm := merge_left (literal (valuationOf q) (219)) (literal (valuationOf q) (427)) (countLit q [219]) (countLit q [220]) (count427 q) 1 (meaning219 q) (meaning427 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 427 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [218]) (l₂ := [219, 220])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [218]) (countLit q [219, 220]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 218 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [218]) (l₂ := [219, 220])
  have hm := merge_left (literal (valuationOf q) (218)) (literal (valuationOf q) (429)) (countLit q [218]) (countLit q [219, 220]) (count429 q) 1 (meaning218 q) (meaning429 q) hs
  change valuationOf q 218 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 429 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [221]) + (countLit q [222]) := List.countP_append (p := literal q) (l₁ := [221]) (l₂ := [222])
  have hm := merge_right (literal (valuationOf q) (222)) (literal (valuationOf q) (431)) (countLit q [221]) (countLit q [222]) (count431 q) 1 (meaning222 q) (meaning431 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 431 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [223]) + (countLit q [224]) := List.countP_append (p := literal q) (l₁ := [223]) (l₂ := [224])
  have hm := merge_left (literal (valuationOf q) (223)) (literal (valuationOf q) (433)) (countLit q [223]) (countLit q [224]) (count433 q) 1 (meaning223 q) (meaning433 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 433 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [221, 222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [221, 222]) (l₂ := [223, 224])
  have hm := merge_right (literal (valuationOf q) (433)) (literal (valuationOf q) (435)) (countLit q [221, 222]) (countLit q [223, 224]) (count435 q) 1 (meaning433 q) (meaning435 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 435 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [221, 222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [221, 222]) (l₂ := [223, 224])
  have hm := merge_left (literal (valuationOf q) (431)) (literal (valuationOf q) (435)) (countLit q [221, 222]) (countLit q [223, 224]) (count435 q) 1 (meaning431 q) (meaning435 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 435 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [218, 219, 220]) + (countLit q [221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220]) (l₂ := [221, 222, 223, 224])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [218, 219, 220]) (countLit q [221, 222, 223, 224]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [218, 219, 220]) + (countLit q [221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220]) (l₂ := [221, 222, 223, 224])
  have hm := merge_left (literal (valuationOf q) (429)) (literal (valuationOf q) (437)) (countLit q [218, 219, 220]) (countLit q [221, 222, 223, 224]) (count437 q) 1 (meaning429 q) (meaning437 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 437 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [231]) + (countLit q [232]) := List.countP_append (p := literal q) (l₁ := [231]) (l₂ := [232])
  have hm := merge_left (literal (valuationOf q) (231)) (literal (valuationOf q) (447)) (countLit q [231]) (countLit q [232]) (count447 q) 1 (meaning231 q) (meaning447 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 447 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_right (literal (valuationOf q) (447)) (literal (valuationOf q) (449)) (countLit q [229, 230]) (countLit q [231, 232]) (count449 q) 1 (meaning447 q) (meaning449 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 449 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [225, 226, 227, 228]) + (countLit q [229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228]) (l₂ := [229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (449)) (literal (valuationOf q) (451)) (countLit q [225, 226, 227, 228]) (countLit q [229, 230, 231, 232]) (count451 q) 1 (meaning449 q) (meaning451 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 451 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (451)) (literal (valuationOf q) (453)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count453 q) 1 (meaning451 q) (meaning453 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 453 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (453)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count453 q) 1 (meaning437 q) (meaning453 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 453 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (455)) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 (meaning425 q) (meaning455 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 455 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (425)) (literal (valuationOf q) (453)) (literal (valuationOf q) (456)) (countLit q [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 1 (meaning425 q) (meaning453 q) (meaning456 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 453 = false ∨ valuation q 456 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E259.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112259
