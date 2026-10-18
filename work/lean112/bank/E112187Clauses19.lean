import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [223, 224, 225]) + (countLit q [226, 227, 228, 229]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225]) (l₂ := [226, 227, 228, 229])
  have hm := merge_left (literal (valuationOf q) (441)) (literal (valuationOf q) (449)) (countLit q [223, 224, 225]) (countLit q [226, 227, 228, 229]) (count449 q) 1 (meaning441 q) (meaning449 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 449 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 447 = false ∨ valuationOf q 450 = true := by
  have hs : count449 q = (countLit q [223, 224, 225]) + (countLit q [226, 227, 228, 229]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225]) (l₂ := [226, 227, 228, 229])
  have hm := merge_two (literal (valuationOf q) (441)) (literal (valuationOf q) (447)) (literal (valuationOf q) (450)) (countLit q [223, 224, 225]) (countLit q [226, 227, 228, 229]) (count449 q) 1 1 (meaning441 q) (meaning447 q) (meaning450 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 447 = false ∨ valuationOf q 450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 447 = false ∨ valuation q 450 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [232]) + (countLit q [233]) := List.countP_append (p := literal q) (l₁ := [232]) (l₂ := [233])
  have hm := merge_right (literal (valuationOf q) (233)) (literal (valuationOf q) (453)) (countLit q [232]) (countLit q [233]) (count453 q) 1 (meaning233 q) (meaning453 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 453 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [230, 231]) + (countLit q [232, 233]) := List.countP_append (p := literal q) (l₁ := [230, 231]) (l₂ := [232, 233])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [230, 231]) (countLit q [232, 233]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [234]) + (countLit q [236]) := List.countP_append (p := literal q) (l₁ := [234]) (l₂ := [236])
  have hm := merge_left (literal (valuationOf q) (234)) (literal (valuationOf q) (457)) (countLit q [234]) (countLit q [236]) (count457 q) 1 (meaning234 q) (meaning457 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 457 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [234, 236]) + (countLit q [237, 238]) := List.countP_append (p := literal q) (l₁ := [234, 236]) (l₂ := [237, 238])
  have hm := merge_left (literal (valuationOf q) (457)) (literal (valuationOf q) (461)) (countLit q [234, 236]) (countLit q [237, 238]) (count461 q) 1 (meaning457 q) (meaning461 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 461 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [230, 231, 232, 233]) + (countLit q [234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [230, 231, 232, 233]) (l₂ := [234, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (461)) (literal (valuationOf q) (463)) (countLit q [230, 231, 232, 233]) (countLit q [234, 236, 237, 238]) (count463 q) 1 (meaning461 q) (meaning463 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 463 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [230, 231, 232, 233]) + (countLit q [234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [230, 231, 232, 233]) (l₂ := [234, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (455)) (literal (valuationOf q) (463)) (countLit q [230, 231, 232, 233]) (countLit q [234, 236, 237, 238]) (count463 q) 1 (meaning455 q) (meaning463 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 463 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true := by
  have hs : count463 q = (countLit q [230, 231, 232, 233]) + (countLit q [234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [230, 231, 232, 233]) (l₂ := [234, 236, 237, 238])
  have hm := merge_two (literal (valuationOf q) (455)) (literal (valuationOf q) (461)) (literal (valuationOf q) (464)) (countLit q [230, 231, 232, 233]) (countLit q [234, 236, 237, 238]) (count463 q) 1 1 (meaning455 q) (meaning461 q) (meaning464 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 461 = false ∨ valuationOf q 464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 461 = false ∨ valuation q 464 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [223, 224, 225, 226, 227, 228, 229]) + (countLit q [230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229]) (l₂ := [230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (463)) (literal (valuationOf q) (465)) (countLit q [223, 224, 225, 226, 227, 228, 229]) (countLit q [230, 231, 232, 233, 234, 236, 237, 238]) (count465 q) 1 (meaning463 q) (meaning465 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 465 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 464 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [223, 224, 225, 226, 227, 228, 229]) + (countLit q [230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229]) (l₂ := [230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (464)) (literal (valuationOf q) (466)) (countLit q [223, 224, 225, 226, 227, 228, 229]) (countLit q [230, 231, 232, 233, 234, 236, 237, 238]) (count465 q) 2 (meaning464 q) (meaning466 q) hs
  change valuationOf q 464 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 464 = false ∨ valuation q 466 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [223, 224, 225, 226, 227, 228, 229]) + (countLit q [230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229]) (l₂ := [230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (449)) (literal (valuationOf q) (465)) (countLit q [223, 224, 225, 226, 227, 228, 229]) (countLit q [230, 231, 232, 233, 234, 236, 237, 238]) (count465 q) 1 (meaning449 q) (meaning465 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 465 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [223, 224, 225, 226, 227, 228, 229]) + (countLit q [230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229]) (l₂ := [230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_two (literal (valuationOf q) (449)) (literal (valuationOf q) (463)) (literal (valuationOf q) (466)) (countLit q [223, 224, 225, 226, 227, 228, 229]) (countLit q [230, 231, 232, 233, 234, 236, 237, 238]) (count465 q) 1 1 (meaning449 q) (meaning463 q) (meaning466 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 463 = false ∨ valuation q 466 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 450 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [223, 224, 225, 226, 227, 228, 229]) + (countLit q [230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229]) (l₂ := [230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (450)) (literal (valuationOf q) (466)) (countLit q [223, 224, 225, 226, 227, 228, 229]) (countLit q [230, 231, 232, 233, 234, 236, 237, 238]) (count465 q) 2 (meaning450 q) (meaning466 q) hs
  change valuationOf q 450 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 450 = false ∨ valuation q 466 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (465)) (literal (valuationOf q) (467)) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) (count467 q) 1 (meaning465 q) (meaning467 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 467 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 466 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (466)) (literal (valuationOf q) (468)) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) (count467 q) 2 (meaning466 q) (meaning468 q) hs
  change valuationOf q 466 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 466 = false ∨ valuation q 468 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (467)) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) (count467 q) 1 (meaning437 q) (meaning467 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 467 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_two (literal (valuationOf q) (437)) (literal (valuationOf q) (465)) (literal (valuationOf q) (468)) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) (count467 q) 1 1 (meaning437 q) (meaning465 q) (meaning468 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 465 = false ∨ valuation q 468 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 438 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (438)) (literal (valuationOf q) (468)) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) (count467 q) 2 (meaning438 q) (meaning468 q) hs
  change valuationOf q 438 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 438 = false ∨ valuation q 468 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) + (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (l₂ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (467)) (literal (valuationOf q) (469)) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) (count469 q) 1 (meaning467 q) (meaning469 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 469 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 468 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) + (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (l₂ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (468)) (literal (valuationOf q) (470)) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) (count469 q) 2 (meaning468 q) (meaning470 q) hs
  change valuationOf q 468 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 468 = false ∨ valuation q 470 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) + (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (l₂ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (409)) (literal (valuationOf q) (469)) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) (count469 q) 1 (meaning409 q) (meaning469 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 469 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 467 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) + (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (l₂ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_two (literal (valuationOf q) (409)) (literal (valuationOf q) (467)) (literal (valuationOf q) (470)) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) (count469 q) 1 1 (meaning409 q) (meaning467 q) (meaning470 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 467 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 467 = false ∨ valuation q 470 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 410 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) + (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (l₂ := [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (410)) (literal (valuationOf q) (470)) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (countLit q [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) (count469 q) 2 (meaning410 q) (meaning470 q) hs
  change valuationOf q 410 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 410 = false ∨ valuation q 470 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 470 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_right (literal (valuationOf q) (470)) (literal (valuationOf q) (472)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) (count471 q) 2 (meaning470 q) (meaning472 q) hs
  change valuationOf q 470 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 470 = false ∨ valuation q 472 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_two (literal (valuationOf q) (353)) (literal (valuationOf q) (469)) (literal (valuationOf q) (472)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) (count471 q) 1 1 (meaning353 q) (meaning469 q) (meaning472 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 469 = false ∨ valuation q 472 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 354 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238])
  have hm := merge_left (literal (valuationOf q) (354)) (literal (valuationOf q) (472)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]) (count471 q) 2 (meaning354 q) (meaning472 q) hs
  change valuationOf q 354 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 354 = false ∨ valuation q 472 = true := counterClause635 (baseVal q)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 472 = false := by
  rw [value472]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count471 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause637 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1447 = true := by
  have hs : count1447 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (1447)) (countLit q [-4]) (countLit q [-6]) (count1447 q) 1 (meaningNeg6 q) (meaning1447 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1447 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1447 = true := by
  have hs : count1447 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1447)) (countLit q [-4]) (countLit q [-6]) (count1447 q) 1 (meaningNeg4 q) (meaning1447 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1447 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1449 = true := by
  have hs : count1449 q = (countLit q [-2]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -6])
  have hm := merge_right (literal (valuationOf q) (1447)) (literal (valuationOf q) (1449)) (countLit q [-2]) (countLit q [-4, -6]) (count1449 q) 1 (meaning1447 q) (meaning1449 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1449 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1449 = true := by
  have hs : count1449 q = (countLit q [-2]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -6])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1449)) (countLit q [-2]) (countLit q [-4, -6]) (count1449 q) 1 (meaningNeg2 q) (meaning1449 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1449 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E187.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112187
