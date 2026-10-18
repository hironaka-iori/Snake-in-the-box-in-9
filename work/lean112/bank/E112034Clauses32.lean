import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [209, 210, 211, 212, 213, 214, 215, 216]) + (countLit q [217, 218, 219, 220, 221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211, 212, 213, 214, 215, 216]) (l₂ := [217, 218, 219, 220, 221, 222, 223, 224])
  have hm := merge_left (literal (valuationOf q) (423)) (literal (valuationOf q) (439)) (countLit q [209, 210, 211, 212, 213, 214, 215, 216]) (countLit q [217, 218, 219, 220, 221, 222, 223, 224]) (count439 q) 1 (meaning423 q) (meaning439 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 439 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 437 = false ∨ valuationOf q 440 = true := by
  have hs : count439 q = (countLit q [209, 210, 211, 212, 213, 214, 215, 216]) + (countLit q [217, 218, 219, 220, 221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [209, 210, 211, 212, 213, 214, 215, 216]) (l₂ := [217, 218, 219, 220, 221, 222, 223, 224])
  have hm := merge_two (literal (valuationOf q) (423)) (literal (valuationOf q) (437)) (literal (valuationOf q) (440)) (countLit q [209, 210, 211, 212, 213, 214, 215, 216]) (countLit q [217, 218, 219, 220, 221, 222, 223, 224]) (count439 q) 1 1 (meaning423 q) (meaning437 q) (meaning440 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 437 = false ∨ valuationOf q 440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 437 = false ∨ valuation q 440 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224])
  have hm := merge_right (literal (valuationOf q) (439)) (literal (valuationOf q) (441)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (count441 q) 1 (meaning439 q) (meaning441 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 441 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 440 = false ∨ valuationOf q 442 = true := by
  have hs : count441 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224])
  have hm := merge_right (literal (valuationOf q) (440)) (literal (valuationOf q) (442)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (count441 q) 2 (meaning440 q) (meaning442 q) hs
  change valuationOf q 440 = false ∨ valuationOf q 442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 440 = false ∨ valuation q 442 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224])
  have hm := merge_left (literal (valuationOf q) (409)) (literal (valuationOf q) (441)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (count441 q) 1 (meaning409 q) (meaning441 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 441 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 439 = false ∨ valuationOf q 442 = true := by
  have hs : count441 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224])
  have hm := merge_two (literal (valuationOf q) (409)) (literal (valuationOf q) (439)) (literal (valuationOf q) (442)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (count441 q) 1 1 (meaning409 q) (meaning439 q) (meaning442 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 439 = false ∨ valuationOf q 442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 439 = false ∨ valuation q 442 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 410 = false ∨ valuationOf q 442 = true := by
  have hs : count441 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224])
  have hm := merge_left (literal (valuationOf q) (410)) (literal (valuationOf q) (442)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (count441 q) 2 (meaning410 q) (meaning442 q) hs
  change valuationOf q 410 = false ∨ valuationOf q 442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 410 = false ∨ valuation q 442 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [227]) + (countLit q [228]) := List.countP_append (p := literal q) (l₁ := [227]) (l₂ := [228])
  have hm := merge_left (literal (valuationOf q) (227)) (literal (valuationOf q) (445)) (countLit q [227]) (countLit q [228]) (count445 q) 1 (meaning227 q) (meaning445 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 445 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_right (literal (valuationOf q) (445)) (literal (valuationOf q) (447)) (countLit q [225, 226]) (countLit q [227, 228]) (count447 q) 1 (meaning445 q) (meaning447 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 447 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 230 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [229]) + (countLit q [230]) := List.countP_append (p := literal q) (l₁ := [229]) (l₂ := [230])
  have hm := merge_right (literal (valuationOf q) (230)) (literal (valuationOf q) (449)) (countLit q [229]) (countLit q [230]) (count449 q) 1 (meaning230 q) (meaning449 q) hs
  change valuationOf q 230 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 449 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [229]) + (countLit q [230]) := List.countP_append (p := literal q) (l₁ := [229]) (l₂ := [230])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (449)) (countLit q [229]) (countLit q [230]) (count449 q) 1 (meaning229 q) (meaning449 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 449 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_left (literal (valuationOf q) (449)) (literal (valuationOf q) (453)) (countLit q [229, 230]) (countLit q [231, 232]) (count453 q) 1 (meaning449 q) (meaning453 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 453 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [225, 226, 227, 228]) + (countLit q [229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228]) (l₂ := [229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [225, 226, 227, 228]) (countLit q [229, 230, 231, 232]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [225, 226, 227, 228]) + (countLit q [229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228]) (l₂ := [229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (447)) (literal (valuationOf q) (455)) (countLit q [225, 226, 227, 228]) (countLit q [229, 230, 231, 232]) (count455 q) 1 (meaning447 q) (meaning455 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 455 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [225, 226, 227, 228]) + (countLit q [229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228]) (l₂ := [229, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (447)) (literal (valuationOf q) (453)) (literal (valuationOf q) (456)) (countLit q [225, 226, 227, 228]) (countLit q [229, 230, 231, 232]) (count455 q) 1 1 (meaning447 q) (meaning453 q) (meaning456 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 453 = false ∨ valuation q 456 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_right (literal (valuationOf q) (234)) (literal (valuationOf q) (457)) (countLit q [233]) (countLit q [234]) (count457 q) 1 (meaning234 q) (meaning457 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 457 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (457)) (countLit q [233]) (countLit q [234]) (count457 q) 1 (meaning233 q) (meaning457 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 457 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_left (literal (valuationOf q) (457)) (literal (valuationOf q) (461)) (countLit q [233, 234]) (countLit q [235, 236]) (count461 q) 1 (meaning457 q) (meaning461 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 461 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [237]) + (countLit q [238]) := List.countP_append (p := literal q) (l₁ := [237]) (l₂ := [238])
  have hm := merge_right (literal (valuationOf q) (238)) (literal (valuationOf q) (463)) (countLit q [237]) (countLit q [238]) (count463 q) 1 (meaning238 q) (meaning463 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 463 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [239]) + (countLit q [240]) := List.countP_append (p := literal q) (l₁ := [239]) (l₂ := [240])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (465)) (countLit q [239]) (countLit q [240]) (count465 q) 1 (meaning239 q) (meaning465 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 465 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_right (literal (valuationOf q) (465)) (literal (valuationOf q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning465 q) (meaning467 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 467 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_left (literal (valuationOf q) (463)) (literal (valuationOf q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning463 q) (meaning467 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 467 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (467)) (literal (valuationOf q) (469)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 1 (meaning467 q) (meaning469 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 469 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (461)) (literal (valuationOf q) (469)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 1 (meaning461 q) (meaning469 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 469 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 467 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_two (literal (valuationOf q) (461)) (literal (valuationOf q) (467)) (literal (valuationOf q) (470)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 1 1 (meaning461 q) (meaning467 q) (meaning470 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 467 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 467 = false ∨ valuation q 470 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (469)) (literal (valuationOf q) (471)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (count471 q) 1 (meaning469 q) (meaning471 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 471 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 470 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (470)) (literal (valuationOf q) (472)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (count471 q) 2 (meaning470 q) (meaning472 q) hs
  change valuationOf q 470 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 470 = false ∨ valuation q 472 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (455)) (literal (valuationOf q) (471)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (count471 q) 1 (meaning455 q) (meaning471 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 471 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_two (literal (valuationOf q) (455)) (literal (valuationOf q) (469)) (literal (valuationOf q) (472)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (count471 q) 1 1 (meaning455 q) (meaning469 q) (meaning472 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 469 = false ∨ valuation q 472 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 456 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (456)) (literal (valuationOf q) (472)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (count471 q) 2 (meaning456 q) (meaning472 q) hs
  change valuationOf q 456 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 456 = false ∨ valuation q 472 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 242 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [241]) + (countLit q [242]) := List.countP_append (p := literal q) (l₁ := [241]) (l₂ := [242])
  have hm := merge_right (literal (valuationOf q) (242)) (literal (valuationOf q) (473)) (countLit q [241]) (countLit q [242]) (count473 q) 1 (meaning242 q) (meaning473 q) hs
  change valuationOf q 242 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 473 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [243]) + (countLit q [244]) := List.countP_append (p := literal q) (l₁ := [243]) (l₂ := [244])
  have hm := merge_right (literal (valuationOf q) (244)) (literal (valuationOf q) (475)) (countLit q [243]) (countLit q [244]) (count475 q) 1 (meaning244 q) (meaning475 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 475 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E034.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112034
