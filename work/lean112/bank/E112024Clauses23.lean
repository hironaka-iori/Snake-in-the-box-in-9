import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_left (literal (valuationOf q) (401)) (literal (valuationOf q) (405)) (countLit q [205, 206]) (countLit q [207, 208]) (count405 q) 1 (meaning401 q) (meaning405 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 405 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [205, 206, 207, 208]) + (countLit q [209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208]) (l₂ := [209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (413)) (countLit q [205, 206, 207, 208]) (countLit q [209, 210, 211, 212]) (count413 q) 1 (meaning405 q) (meaning413 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 413 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (399)) (literal (valuationOf q) (415)) (countLit q [198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 (meaning399 q) (meaning415 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 415 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 413 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (399)) (literal (valuationOf q) (413)) (literal (valuationOf q) (416)) (countLit q [198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 1 (meaning399 q) (meaning413 q) (meaning416 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 413 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 413 = false ∨ valuation q 416 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (415)) (literal (valuationOf q) (417)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 (meaning415 q) (meaning417 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 417 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 416 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (416)) (literal (valuationOf q) (418)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 2 (meaning416 q) (meaning418 q) hs
  change valuationOf q 416 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 416 = false ∨ valuation q 418 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (417)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 (meaning387 q) (meaning417 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 417 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (387)) (literal (valuationOf q) (415)) (literal (valuationOf q) (418)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 1 (meaning387 q) (meaning415 q) (meaning418 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 415 = false ∨ valuation q 418 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (388)) (literal (valuationOf q) (418)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 2 (meaning388 q) (meaning418 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 418 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [213]) + (countLit q [214, 215]) := List.countP_append (p := literal q) (l₁ := [213]) (l₂ := [214, 215])
  have hm := merge_left (literal (valuationOf q) (213)) (literal (valuationOf q) (421)) (countLit q [213]) (countLit q [214, 215]) (count421 q) 1 (meaning213 q) (meaning421 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 421 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 218 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [218]) + (countLit q [219]) := List.countP_append (p := literal q) (l₁ := [218]) (l₂ := [219])
  have hm := merge_left (literal (valuationOf q) (218)) (literal (valuationOf q) (425)) (countLit q [218]) (countLit q [219]) (count425 q) 1 (meaning218 q) (meaning425 q) hs
  change valuationOf q 218 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 425 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [216, 217]) + (countLit q [218, 219]) := List.countP_append (p := literal q) (l₁ := [216, 217]) (l₂ := [218, 219])
  have hm := merge_right (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (countLit q [216, 217]) (countLit q [218, 219]) (count427 q) 1 (meaning425 q) (meaning427 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [213, 214, 215]) + (countLit q [216, 217, 218, 219]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215]) (l₂ := [216, 217, 218, 219])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [213, 214, 215]) (countLit q [216, 217, 218, 219]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [213, 214, 215]) + (countLit q [216, 217, 218, 219]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215]) (l₂ := [216, 217, 218, 219])
  have hm := merge_left (literal (valuationOf q) (421)) (literal (valuationOf q) (429)) (countLit q [213, 214, 215]) (countLit q [216, 217, 218, 219]) (count429 q) 1 (meaning421 q) (meaning429 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 429 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [220]) + (countLit q [221]) := List.countP_append (p := literal q) (l₁ := [220]) (l₂ := [221])
  have hm := merge_right (literal (valuationOf q) (221)) (literal (valuationOf q) (431)) (countLit q [220]) (countLit q [221]) (count431 q) 1 (meaning221 q) (meaning431 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 431 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [222]) + (countLit q [223]) := List.countP_append (p := literal q) (l₁ := [222]) (l₂ := [223])
  have hm := merge_left (literal (valuationOf q) (222)) (literal (valuationOf q) (433)) (countLit q [222]) (countLit q [223]) (count433 q) 1 (meaning222 q) (meaning433 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 433 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [220, 221]) + (countLit q [222, 223]) := List.countP_append (p := literal q) (l₁ := [220, 221]) (l₂ := [222, 223])
  have hm := merge_right (literal (valuationOf q) (433)) (literal (valuationOf q) (435)) (countLit q [220, 221]) (countLit q [222, 223]) (count435 q) 1 (meaning433 q) (meaning435 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 435 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [220, 221]) + (countLit q [222, 223]) := List.countP_append (p := literal q) (l₁ := [220, 221]) (l₂ := [222, 223])
  have hm := merge_left (literal (valuationOf q) (431)) (literal (valuationOf q) (435)) (countLit q [220, 221]) (countLit q [222, 223]) (count435 q) 1 (meaning431 q) (meaning435 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 435 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [224]) + (countLit q [225]) := List.countP_append (p := literal q) (l₁ := [224]) (l₂ := [225])
  have hm := merge_right (literal (valuationOf q) (225)) (literal (valuationOf q) (437)) (countLit q [224]) (countLit q [225]) (count437 q) 1 (meaning225 q) (meaning437 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 437 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [224, 225]) + (countLit q [226, 227]) := List.countP_append (p := literal q) (l₁ := [224, 225]) (l₂ := [226, 227])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (441)) (countLit q [224, 225]) (countLit q [226, 227]) (count441 q) 1 (meaning437 q) (meaning441 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 441 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [220, 221, 222, 223]) + (countLit q [224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [220, 221, 222, 223]) (l₂ := [224, 225, 226, 227])
  have hm := merge_right (literal (valuationOf q) (441)) (literal (valuationOf q) (443)) (countLit q [220, 221, 222, 223]) (countLit q [224, 225, 226, 227]) (count443 q) 1 (meaning441 q) (meaning443 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 443 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [220, 221, 222, 223]) + (countLit q [224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [220, 221, 222, 223]) (l₂ := [224, 225, 226, 227])
  have hm := merge_left (literal (valuationOf q) (435)) (literal (valuationOf q) (443)) (countLit q [220, 221, 222, 223]) (countLit q [224, 225, 226, 227]) (count443 q) 1 (meaning435 q) (meaning443 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 443 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [213, 214, 215, 216, 217, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227])
  have hm := merge_right (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (countLit q [213, 214, 215, 216, 217, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) (count445 q) 1 (meaning443 q) (meaning445 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [213, 214, 215, 216, 217, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227])
  have hm := merge_left (literal (valuationOf q) (429)) (literal (valuationOf q) (445)) (countLit q [213, 214, 215, 216, 217, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) (count445 q) 1 (meaning429 q) (meaning445 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 445 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 443 = false ∨ valuationOf q 446 = true := by
  have hs : count445 q = (countLit q [213, 214, 215, 216, 217, 218, 219]) + (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215, 216, 217, 218, 219]) (l₂ := [220, 221, 222, 223, 224, 225, 226, 227])
  have hm := merge_two (literal (valuationOf q) (429)) (literal (valuationOf q) (443)) (literal (valuationOf q) (446)) (countLit q [213, 214, 215, 216, 217, 218, 219]) (countLit q [220, 221, 222, 223, 224, 225, 226, 227]) (count445 q) 1 1 (meaning429 q) (meaning443 q) (meaning446 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 443 = false ∨ valuationOf q 446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 443 = false ∨ valuation q 446 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_right (literal (valuationOf q) (234)) (literal (valuationOf q) (453)) (countLit q [233]) (countLit q [234]) (count453 q) 1 (meaning234 q) (meaning453 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 453 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [231, 232]) + (countLit q [233, 234]) := List.countP_append (p := literal q) (l₁ := [231, 232]) (l₂ := [233, 234])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [231, 232]) (countLit q [233, 234]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [228, 229, 230]) + (countLit q [231, 232, 233, 234]) := List.countP_append (p := literal q) (l₁ := [228, 229, 230]) (l₂ := [231, 232, 233, 234])
  have hm := merge_right (literal (valuationOf q) (455)) (literal (valuationOf q) (457)) (countLit q [228, 229, 230]) (countLit q [231, 232, 233, 234]) (count457 q) 1 (meaning455 q) (meaning457 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 457 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [235]) + (countLit q [236]) := List.countP_append (p := literal q) (l₁ := [235]) (l₂ := [236])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (459)) (countLit q [235]) (countLit q [236]) (count459 q) 1 (meaning235 q) (meaning459 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 459 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [235, 236]) + (countLit q [237, 238]) := List.countP_append (p := literal q) (l₁ := [235, 236]) (l₂ := [237, 238])
  have hm := merge_left (literal (valuationOf q) (459)) (literal (valuationOf q) (463)) (countLit q [235, 236]) (countLit q [237, 238]) (count463 q) 1 (meaning459 q) (meaning463 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 463 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [235, 236, 237, 238]) + (countLit q [239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [235, 236, 237, 238]) (l₂ := [239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (463)) (literal (valuationOf q) (471)) (countLit q [235, 236, 237, 238]) (countLit q [239, 240, 241, 242]) (count471 q) 1 (meaning463 q) (meaning471 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 471 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E024.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112024
