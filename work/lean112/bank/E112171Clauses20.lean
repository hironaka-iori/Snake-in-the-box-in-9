import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [221, 222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [221, 222]) (l₂ := [223, 224])
  have hm := merge_right (literal (valuationOf q) (433)) (literal (valuationOf q) (435)) (countLit q [221, 222]) (countLit q [223, 224]) (count435 q) 1 (meaning433 q) (meaning435 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 435 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_right (literal (valuationOf q) (226)) (literal (valuationOf q) (437)) (countLit q [225]) (countLit q [226]) (count437 q) 1 (meaning226 q) (meaning437 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 437 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_left (literal (valuationOf q) (225)) (literal (valuationOf q) (437)) (countLit q [225]) (countLit q [226]) (count437 q) 1 (meaning225 q) (meaning437 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 437 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 226 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_two (literal (valuationOf q) (225)) (literal (valuationOf q) (226)) (literal (valuationOf q) (438)) (countLit q [225]) (countLit q [226]) (count437 q) 1 1 (meaning225 q) (meaning226 q) (meaning438 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 226 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 226 = false ∨ valuation q 438 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (441)) (countLit q [225, 226]) (countLit q [227, 228]) (count441 q) 1 (meaning437 q) (meaning441 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 441 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 438 = false ∨ valuationOf q 442 = true := by
  have hs : count441 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_left (literal (valuationOf q) (438)) (literal (valuationOf q) (442)) (countLit q [225, 226]) (countLit q [227, 228]) (count441 q) 2 (meaning438 q) (meaning442 q) hs
  change valuationOf q 438 = false ∨ valuationOf q 442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 438 = false ∨ valuation q 442 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [221, 222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [221, 222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (441)) (literal (valuationOf q) (443)) (countLit q [221, 222, 223, 224]) (countLit q [225, 226, 227, 228]) (count443 q) 1 (meaning441 q) (meaning443 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 443 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 442 = false ∨ valuationOf q 444 = true := by
  have hs : count443 q = (countLit q [221, 222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [221, 222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (442)) (literal (valuationOf q) (444)) (countLit q [221, 222, 223, 224]) (countLit q [225, 226, 227, 228]) (count443 q) 2 (meaning442 q) (meaning444 q) hs
  change valuationOf q 442 = false ∨ valuationOf q 444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 442 = false ∨ valuation q 444 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [221, 222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [221, 222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (435)) (literal (valuationOf q) (443)) (countLit q [221, 222, 223, 224]) (countLit q [225, 226, 227, 228]) (count443 q) 1 (meaning435 q) (meaning443 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 443 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [214, 215, 216, 217, 218, 219, 220]) + (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220]) (l₂ := [221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (countLit q [214, 215, 216, 217, 218, 219, 220]) (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) (count445 q) 1 (meaning443 q) (meaning445 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 444 = false ∨ valuationOf q 446 = true := by
  have hs : count445 q = (countLit q [214, 215, 216, 217, 218, 219, 220]) + (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220]) (l₂ := [221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (444)) (literal (valuationOf q) (446)) (countLit q [214, 215, 216, 217, 218, 219, 220]) (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) (count445 q) 2 (meaning444 q) (meaning446 q) hs
  change valuationOf q 444 = false ∨ valuationOf q 446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 444 = false ∨ valuation q 446 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [214, 215, 216, 217, 218, 219, 220]) + (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217, 218, 219, 220]) (l₂ := [221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (429)) (literal (valuationOf q) (445)) (countLit q [214, 215, 216, 217, 218, 219, 220]) (countLit q [221, 222, 223, 224, 225, 226, 227, 228]) (count445 q) 1 (meaning429 q) (meaning445 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 445 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (445)) (literal (valuationOf q) (447)) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count447 q) 1 (meaning445 q) (meaning447 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 447 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 446 = false ∨ valuationOf q 448 = true := by
  have hs : count447 q = (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (446)) (literal (valuationOf q) (448)) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count447 q) 2 (meaning446 q) (meaning448 q) hs
  change valuationOf q 446 = false ∨ valuationOf q 448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 446 = false ∨ valuation q 448 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (447)) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count447 q) 1 (meaning417 q) (meaning447 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 447 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 445 = false ∨ valuationOf q 448 = true := by
  have hs : count447 q = (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_two (literal (valuationOf q) (417)) (literal (valuationOf q) (445)) (literal (valuationOf q) (448)) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count447 q) 1 1 (meaning417 q) (meaning445 q) (meaning448 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 445 = false ∨ valuationOf q 448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 445 = false ∨ valuation q 448 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 418 = false ∨ valuationOf q 448 = true := by
  have hs : count447 q = (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (418)) (literal (valuationOf q) (448)) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count447 q) 2 (meaning418 q) (meaning448 q) hs
  change valuationOf q 418 = false ∨ valuationOf q 448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 448 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (447)) (literal (valuationOf q) (449)) (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count449 q) 1 (meaning447 q) (meaning449 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 449 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 448 = false ∨ valuationOf q 450 = true := by
  have hs : count449 q = (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (448)) (literal (valuationOf q) (450)) (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count449 q) 2 (meaning448 q) (meaning450 q) hs
  change valuationOf q 448 = false ∨ valuationOf q 450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 448 = false ∨ valuation q 450 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (449)) (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count449 q) 1 (meaning391 q) (meaning449 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 449 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 447 = false ∨ valuationOf q 450 = true := by
  have hs : count449 q = (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_two (literal (valuationOf q) (391)) (literal (valuationOf q) (447)) (literal (valuationOf q) (450)) (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count449 q) 1 1 (meaning391 q) (meaning447 q) (meaning450 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 447 = false ∨ valuationOf q 450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 447 = false ∨ valuation q 450 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 392 = false ∨ valuationOf q 450 = true := by
  have hs : count449 q = (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (392)) (literal (valuationOf q) (450)) (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count449 q) 2 (meaning392 q) (meaning450 q) hs
  change valuationOf q 392 = false ∨ valuationOf q 450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 392 = false ∨ valuation q 450 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 450 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (450)) (literal (valuationOf q) (452)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count451 q) 2 (meaning450 q) (meaning452 q) hs
  change valuationOf q 450 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 450 = false ∨ valuation q 452 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 449 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_two (literal (valuationOf q) (337)) (literal (valuationOf q) (449)) (literal (valuationOf q) (452)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count451 q) 1 1 (meaning337 q) (meaning449 q) (meaning452 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 449 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 449 = false ∨ valuation q 452 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 338 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (338)) (literal (valuationOf q) (452)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count451 q) 2 (meaning338 q) (meaning452 q) hs
  change valuationOf q 338 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 338 = false ∨ valuation q 452 = true := counterClause665 (baseVal q)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 452 = false := by
  rw [value452]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count451 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 117 = true ∨ valuation q 118 = true ∨ valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 121 = true ∨ valuation q 122 = true ∨ valuation q 123 = true ∨ valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 211 = true ∨ valuation q 212 = true ∨ valuation q 213 = true ∨ valuation q 214 = true ∨ valuation q 215 = true ∨ valuation q 216 = true ∨ valuation q 217 = true ∨ valuation q 218 = true ∨ valuation q 219 = true ∨ valuation q 220 = true ∨ valuation q 221 = true ∨ valuation q 222 = true ∨ valuation q 223 = true ∨ valuation q 224 = true ∨ valuation q 225 = true ∨ valuation q 226 = true ∨ valuation q 227 = true ∨ valuation q 228 = true := by
  rw [value115, value116, value117, value118, value119, value120, value121, value122, value123, value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value211, value212, value213, value214, value215, value216, value217, value218, value219, value220, value221, value222, value223, value224, value225, value226, value227, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause668 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1365)) (countLit q [-4]) (countLit q [-5]) (count1365 q) 1 (meaningNeg5 q) (meaning1365 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1365 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1365)) (countLit q [-4]) (countLit q [-5]) (count1365 q) 1 (meaningNeg4 q) (meaning1365 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1365 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1366)) (countLit q [-4]) (countLit q [-5]) (count1365 q) 1 1 (meaningNeg4 q) (meaningNeg5 q) (meaning1366 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 1366 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1367 = true := by
  have hs : count1367 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1365)) (literal (valuationOf q) (1367)) (countLit q [-2]) (countLit q [-4, -5]) (count1367 q) 1 (meaning1365 q) (meaning1367 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1367 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1368 = true := by
  have hs : count1367 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1366)) (literal (valuationOf q) (1368)) (countLit q [-2]) (countLit q [-4, -5]) (count1367 q) 2 (meaning1366 q) (meaning1368 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1368 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E171.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112171
