import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_right (literal (valuationOf q) (441)) (literal (valuationOf q) (443)) (countLit q [225, 226]) (countLit q [227, 228]) (count443 q) 1 (meaning441 q) (meaning443 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 443 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (countLit q [222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 (meaning443 q) (meaning445 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 230 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [229]) + (countLit q [230]) := List.countP_append (p := literal q) (l₁ := [229]) (l₂ := [230])
  have hm := merge_right (literal (valuationOf q) (230)) (literal (valuationOf q) (447)) (countLit q [229]) (countLit q [230]) (count447 q) 1 (meaning230 q) (meaning447 q) hs
  change valuationOf q 230 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 447 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_left (literal (valuationOf q) (447)) (literal (valuationOf q) (451)) (countLit q [229, 230]) (countLit q [231, 232]) (count451 q) 1 (meaning447 q) (meaning451 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 451 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_right (literal (valuationOf q) (234)) (literal (valuationOf q) (453)) (countLit q [233]) (countLit q [234]) (count453 q) 1 (meaning234 q) (meaning453 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 453 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 236 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [235]) + (countLit q [236]) := List.countP_append (p := literal q) (l₁ := [235]) (l₂ := [236])
  have hm := merge_right (literal (valuationOf q) (236)) (literal (valuationOf q) (455)) (countLit q [235]) (countLit q [236]) (count455 q) 1 (meaning236 q) (meaning455 q) hs
  change valuationOf q 236 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 455 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_right (literal (valuationOf q) (455)) (literal (valuationOf q) (457)) (countLit q [233, 234]) (countLit q [235, 236]) (count457 q) 1 (meaning455 q) (meaning457 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 457 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_left (literal (valuationOf q) (453)) (literal (valuationOf q) (457)) (countLit q [233, 234]) (countLit q [235, 236]) (count457 q) 1 (meaning453 q) (meaning457 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 457 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (457)) (literal (valuationOf q) (459)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count459 q) 1 (meaning457 q) (meaning459 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 459 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (451)) (literal (valuationOf q) (459)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count459 q) 1 (meaning451 q) (meaning459 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 459 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (459)) (literal (valuationOf q) (461)) (countLit q [222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (count461 q) 1 (meaning459 q) (meaning461 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 461 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (445)) (literal (valuationOf q) (461)) (countLit q [222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (count461 q) 1 (meaning445 q) (meaning461 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 461 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (461)) (literal (valuationOf q) (463)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 1 (meaning461 q) (meaning463 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 463 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (433)) (literal (valuationOf q) (463)) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count463 q) 1 (meaning433 q) (meaning463 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 463 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (463)) (literal (valuationOf q) (465)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 1 (meaning463 q) (meaning465 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 465 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (465)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 1 (meaning405 q) (meaning465 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 465 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (405)) (literal (valuationOf q) (463)) (literal (valuationOf q) (466)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 1 1 (meaning405 q) (meaning463 q) (meaning466 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 463 = false ∨ valuation q 466 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 406 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (406)) (literal (valuationOf q) (466)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count465 q) 2 (meaning406 q) (meaning466 q) hs
  change valuationOf q 406 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 406 = false ∨ valuation q 466 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 466 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (466)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 2 (meaning466 q) (meaning468 q) hs
  change valuationOf q 466 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 466 = false ∨ valuation q 468 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (349)) (literal (valuationOf q) (465)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 1 1 (meaning349 q) (meaning465 q) (meaning468 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 465 = false ∨ valuation q 468 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 350 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [119, 120, 121, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (350)) (literal (valuationOf q) (468)) (countLit q [119, 120, 121, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]) (count467 q) 2 (meaning350 q) (meaning468 q) hs
  change valuationOf q 350 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 350 = false ∨ valuation q 468 = true := counterClause565 (baseVal q)

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 468 = false := by
  rw [value468]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count467 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause567 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 801 = true := by
  have hs : count801 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_right (literal (valuationOf q) (-4)) (literal (valuationOf q) (801)) (countLit q [-3]) (countLit q [-4]) (count801 q) 1 (meaningNeg4 q) (meaning801 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 801 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 801 = true := by
  have hs : count801 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (801)) (countLit q [-3]) (countLit q [-4]) (count801 q) 1 (meaningNeg3 q) (meaning801 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 801 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 4 = true ∨ valuationOf q 802 = true := by
  have hs : count801 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-4)) (literal (valuationOf q) (802)) (countLit q [-3]) (countLit q [-4]) (count801 q) 1 1 (meaningNeg3 q) (meaningNeg4 q) (meaning802 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 4)) = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 4 = true ∨ valuation q 802 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 803 = true := by
  have hs : count803 q = (countLit q [-1]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -4])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (803)) (countLit q [-1]) (countLit q [-3, -4]) (count803 q) 1 (meaningNeg1 q) (meaning803 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 803 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 801 = false ∨ valuationOf q 804 = true := by
  have hs : count803 q = (countLit q [-1]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -4])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (801)) (literal (valuationOf q) (804)) (countLit q [-1]) (countLit q [-3, -4]) (count803 q) 1 1 (meaningNeg1 q) (meaning801 q) (meaning804 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 801 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 801 = false ∨ valuation q 804 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 802 = false ∨ valuationOf q 805 = true := by
  have hs : count803 q = (countLit q [-1]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -4])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (802)) (literal (valuationOf q) (805)) (countLit q [-1]) (countLit q [-3, -4]) (count803 q) 1 2 (meaningNeg1 q) (meaning802 q) (meaning805 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 802 = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 802 = false ∨ valuation q 805 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 806 = true := by
  have hs : count806 q = (countLit q [-5]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-5)) (literal (valuationOf q) (806)) (countLit q [-5]) (countLit q [-7]) (count806 q) 1 (meaningNeg5 q) (meaning806 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 806 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 808 = true := by
  have hs : count808 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (808)) (countLit q [-9]) (countLit q [-10]) (count808 q) 1 (meaningNeg10 q) (meaning808 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 808 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 808 = true := by
  have hs : count808 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (808)) (countLit q [-9]) (countLit q [-10]) (count808 q) 1 (meaningNeg9 q) (meaning808 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 808 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 10 = true ∨ valuationOf q 809 = true := by
  have hs : count808 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (809)) (countLit q [-9]) (countLit q [-10]) (count808 q) 1 1 (meaningNeg9 q) (meaningNeg10 q) (meaning809 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 10 = true ∨ valuation q 809 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E159.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112159
