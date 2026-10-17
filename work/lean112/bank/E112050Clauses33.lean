import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [225, 226, 227, 228]) + (countLit q [229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228]) (l₂ := [229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (447)) (literal (valuationOf q) (455)) (countLit q [225, 226, 227, 228]) (countLit q [229, 230, 231, 232]) (count455 q) 1 (meaning447 q) (meaning455 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 455 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 448 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [225, 226, 227, 228]) + (countLit q [229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228]) (l₂ := [229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (448)) (literal (valuationOf q) (456)) (countLit q [225, 226, 227, 228]) (countLit q [229, 230, 231, 232]) (count455 q) 2 (meaning448 q) (meaning456 q) hs
  change valuationOf q 448 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 448 = false ∨ valuation q 456 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (457)) (countLit q [233]) (countLit q [234]) (count457 q) 1 (meaning233 q) (meaning457 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 457 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_left (literal (valuationOf q) (457)) (literal (valuationOf q) (461)) (countLit q [233, 234]) (countLit q [235, 236]) (count461 q) 1 (meaning457 q) (meaning461 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 461 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [237]) + (countLit q [238]) := List.countP_append (p := literal q) (l₁ := [237]) (l₂ := [238])
  have hm := merge_right (literal (valuationOf q) (238)) (literal (valuationOf q) (463)) (countLit q [237]) (countLit q [238]) (count463 q) 1 (meaning238 q) (meaning463 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 463 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_left (literal (valuationOf q) (463)) (literal (valuationOf q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning463 q) (meaning467 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 467 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (467)) (literal (valuationOf q) (469)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 1 (meaning467 q) (meaning469 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 469 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (461)) (literal (valuationOf q) (469)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 1 (meaning461 q) (meaning469 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 469 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (469)) (literal (valuationOf q) (471)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (count471 q) 1 (meaning469 q) (meaning471 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 471 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (455)) (literal (valuationOf q) (471)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (count471 q) 1 (meaning455 q) (meaning471 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 471 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_two (literal (valuationOf q) (455)) (literal (valuationOf q) (469)) (literal (valuationOf q) (472)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (count471 q) 1 1 (meaning455 q) (meaning469 q) (meaning472 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 469 = false ∨ valuation q 472 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 456 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (456)) (literal (valuationOf q) (472)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (count471 q) 2 (meaning456 q) (meaning472 q) hs
  change valuationOf q 456 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 456 = false ∨ valuation q 472 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [243]) + (countLit q [244]) := List.countP_append (p := literal q) (l₁ := [243]) (l₂ := [244])
  have hm := merge_right (literal (valuationOf q) (244)) (literal (valuationOf q) (475)) (countLit q [243]) (countLit q [244]) (count475 q) 1 (meaning244 q) (meaning475 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 475 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [241, 242]) + (countLit q [243, 244]) := List.countP_append (p := literal q) (l₁ := [241, 242]) (l₂ := [243, 244])
  have hm := merge_right (literal (valuationOf q) (475)) (literal (valuationOf q) (477)) (countLit q [241, 242]) (countLit q [243, 244]) (count477 q) 1 (meaning475 q) (meaning477 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 477 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 248 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [247]) + (countLit q [248]) := List.countP_append (p := literal q) (l₁ := [247]) (l₂ := [248])
  have hm := merge_right (literal (valuationOf q) (248)) (literal (valuationOf q) (481)) (countLit q [247]) (countLit q [248]) (count481 q) 1 (meaning248 q) (meaning481 q) hs
  change valuationOf q 248 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 481 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [245, 246]) + (countLit q [247, 248]) := List.countP_append (p := literal q) (l₁ := [245, 246]) (l₂ := [247, 248])
  have hm := merge_right (literal (valuationOf q) (481)) (literal (valuationOf q) (483)) (countLit q [245, 246]) (countLit q [247, 248]) (count483 q) 1 (meaning481 q) (meaning483 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 483 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 483 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (483)) (literal (valuationOf q) (485)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count485 q) 1 (meaning483 q) (meaning485 q) hs
  change valuationOf q 483 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 483 = false ∨ valuation q 485 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (477)) (literal (valuationOf q) (485)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count485 q) 1 (meaning477 q) (meaning485 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 485 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 250 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [249]) + (countLit q [250]) := List.countP_append (p := literal q) (l₁ := [249]) (l₂ := [250])
  have hm := merge_right (literal (valuationOf q) (250)) (literal (valuationOf q) (487)) (countLit q [249]) (countLit q [250]) (count487 q) 1 (meaning250 q) (meaning487 q) hs
  change valuationOf q 250 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 250 = false ∨ valuation q 487 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 491 = true := by
  have hs : count491 q = (countLit q [249, 250]) + (countLit q [251, 252]) := List.countP_append (p := literal q) (l₁ := [249, 250]) (l₂ := [251, 252])
  have hm := merge_left (literal (valuationOf q) (487)) (literal (valuationOf q) (491)) (countLit q [249, 250]) (countLit q [251, 252]) (count491 q) 1 (meaning487 q) (meaning491 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 491 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 254 = false ∨ valuationOf q 493 = true := by
  have hs : count493 q = (countLit q [253]) + (countLit q [254]) := List.countP_append (p := literal q) (l₁ := [253]) (l₂ := [254])
  have hm := merge_right (literal (valuationOf q) (254)) (literal (valuationOf q) (493)) (countLit q [253]) (countLit q [254]) (count493 q) 1 (meaning254 q) (meaning493 q) hs
  change valuationOf q 254 = false ∨ valuationOf q 493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 254 = false ∨ valuation q 493 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 493 = false ∨ valuationOf q 497 = true := by
  have hs : count497 q = (countLit q [253, 254]) + (countLit q [255, 256]) := List.countP_append (p := literal q) (l₁ := [253, 254]) (l₂ := [255, 256])
  have hm := merge_left (literal (valuationOf q) (493)) (literal (valuationOf q) (497)) (countLit q [253, 254]) (countLit q [255, 256]) (count497 q) 1 (meaning493 q) (meaning497 q) hs
  change valuationOf q 493 = false ∨ valuationOf q 497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 493 = false ∨ valuation q 497 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 497 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [249, 250, 251, 252]) + (countLit q [253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [249, 250, 251, 252]) (l₂ := [253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (497)) (literal (valuationOf q) (499)) (countLit q [249, 250, 251, 252]) (countLit q [253, 254, 255, 256]) (count499 q) 1 (meaning497 q) (meaning499 q) hs
  change valuationOf q 497 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 497 = false ∨ valuation q 499 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 491 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [249, 250, 251, 252]) + (countLit q [253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [249, 250, 251, 252]) (l₂ := [253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (491)) (literal (valuationOf q) (499)) (countLit q [249, 250, 251, 252]) (countLit q [253, 254, 255, 256]) (count499 q) 1 (meaning491 q) (meaning499 q) hs
  change valuationOf q 491 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 491 = false ∨ valuation q 499 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 499 = false ∨ valuationOf q 501 = true := by
  have hs : count501 q = (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) + (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244, 245, 246, 247, 248]) (l₂ := [249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (499)) (literal (valuationOf q) (501)) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) (count501 q) 1 (meaning499 q) (meaning501 q) hs
  change valuationOf q 499 = false ∨ valuationOf q 501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 499 = false ∨ valuation q 501 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 485 = false ∨ valuationOf q 501 = true := by
  have hs : count501 q = (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) + (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244, 245, 246, 247, 248]) (l₂ := [249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (485)) (literal (valuationOf q) (501)) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) (count501 q) 1 (meaning485 q) (meaning501 q) hs
  change valuationOf q 485 = false ∨ valuationOf q 501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 485 = false ∨ valuation q 501 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 485 = false ∨ valuationOf q 499 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) + (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244, 245, 246, 247, 248]) (l₂ := [249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_two (literal (valuationOf q) (485)) (literal (valuationOf q) (499)) (literal (valuationOf q) (502)) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) (count501 q) 1 1 (meaning485 q) (meaning499 q) (meaning502 q) hs
  change valuationOf q 485 = false ∨ valuationOf q 499 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 485 = false ∨ valuation q 499 = false ∨ valuation q 502 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 501 = false ∨ valuationOf q 503 = true := by
  have hs : count503 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (501)) (literal (valuationOf q) (503)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count503 q) 1 (meaning501 q) (meaning503 q) hs
  change valuationOf q 501 = false ∨ valuationOf q 503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 501 = false ∨ valuation q 503 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 502 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (502)) (literal (valuationOf q) (504)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count503 q) 2 (meaning502 q) (meaning504 q) hs
  change valuationOf q 502 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 502 = false ∨ valuation q 504 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 503 = true := by
  have hs : count503 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (471)) (literal (valuationOf q) (503)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count503 q) 1 (meaning471 q) (meaning503 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 503 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 501 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_two (literal (valuationOf q) (471)) (literal (valuationOf q) (501)) (literal (valuationOf q) (504)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count503 q) 1 1 (meaning471 q) (meaning501 q) (meaning504 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 501 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 501 = false ∨ valuation q 504 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 472 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (472)) (literal (valuationOf q) (504)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count503 q) 2 (meaning472 q) (meaning504 q) hs
  change valuationOf q 472 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 472 = false ∨ valuation q 504 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E050.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112050
