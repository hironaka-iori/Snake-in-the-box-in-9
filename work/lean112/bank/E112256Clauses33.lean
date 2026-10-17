import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [243]) + (countLit q [244]) := List.countP_append (p := literal q) (l₁ := [243]) (l₂ := [244])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (475)) (countLit q [243]) (countLit q [244]) (count475 q) 1 (meaning243 q) (meaning475 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 475 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [245]) + (countLit q [246]) := List.countP_append (p := literal q) (l₁ := [245]) (l₂ := [246])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (477)) (countLit q [245]) (countLit q [246]) (count477 q) 1 (meaning245 q) (meaning477 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 477 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [243, 244]) + (countLit q [245, 246]) := List.countP_append (p := literal q) (l₁ := [243, 244]) (l₂ := [245, 246])
  have hm := merge_right (literal (valuationOf q) (477)) (literal (valuationOf q) (479)) (countLit q [243, 244]) (countLit q [245, 246]) (count479 q) 1 (meaning477 q) (meaning479 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 479 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [243, 244]) + (countLit q [245, 246]) := List.countP_append (p := literal q) (l₁ := [243, 244]) (l₂ := [245, 246])
  have hm := merge_left (literal (valuationOf q) (475)) (literal (valuationOf q) (479)) (countLit q [243, 244]) (countLit q [245, 246]) (count479 q) 1 (meaning475 q) (meaning479 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 479 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [243, 244]) + (countLit q [245, 246]) := List.countP_append (p := literal q) (l₁ := [243, 244]) (l₂ := [245, 246])
  have hm := merge_two (literal (valuationOf q) (475)) (literal (valuationOf q) (477)) (literal (valuationOf q) (480)) (countLit q [243, 244]) (countLit q [245, 246]) (count479 q) 1 1 (meaning475 q) (meaning477 q) (meaning480 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 477 = false ∨ valuation q 480 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 479 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [239, 240, 241, 242]) + (countLit q [243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242]) (l₂ := [243, 244, 245, 246])
  have hm := merge_right (literal (valuationOf q) (479)) (literal (valuationOf q) (481)) (countLit q [239, 240, 241, 242]) (countLit q [243, 244, 245, 246]) (count481 q) 1 (meaning479 q) (meaning481 q) hs
  change valuationOf q 479 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 479 = false ∨ valuation q 481 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 480 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [239, 240, 241, 242]) + (countLit q [243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242]) (l₂ := [243, 244, 245, 246])
  have hm := merge_right (literal (valuationOf q) (480)) (literal (valuationOf q) (482)) (countLit q [239, 240, 241, 242]) (countLit q [243, 244, 245, 246]) (count481 q) 2 (meaning480 q) (meaning482 q) hs
  change valuationOf q 480 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 480 = false ∨ valuation q 482 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [239, 240, 241, 242]) + (countLit q [243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242]) (l₂ := [243, 244, 245, 246])
  have hm := merge_left (literal (valuationOf q) (473)) (literal (valuationOf q) (481)) (countLit q [239, 240, 241, 242]) (countLit q [243, 244, 245, 246]) (count481 q) 1 (meaning473 q) (meaning481 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 481 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [247]) + (countLit q [248]) := List.countP_append (p := literal q) (l₁ := [247]) (l₂ := [248])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (483)) (countLit q [247]) (countLit q [248]) (count483 q) 1 (meaning247 q) (meaning483 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 483 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [249]) + (countLit q [250]) := List.countP_append (p := literal q) (l₁ := [249]) (l₂ := [250])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (485)) (countLit q [249]) (countLit q [250]) (count485 q) 1 (meaning249 q) (meaning485 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 485 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 485 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [247, 248]) + (countLit q [249, 250]) := List.countP_append (p := literal q) (l₁ := [247, 248]) (l₂ := [249, 250])
  have hm := merge_right (literal (valuationOf q) (485)) (literal (valuationOf q) (487)) (countLit q [247, 248]) (countLit q [249, 250]) (count487 q) 1 (meaning485 q) (meaning487 q) hs
  change valuationOf q 485 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 485 = false ∨ valuation q 487 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 483 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [247, 248]) + (countLit q [249, 250]) := List.countP_append (p := literal q) (l₁ := [247, 248]) (l₂ := [249, 250])
  have hm := merge_left (literal (valuationOf q) (483)) (literal (valuationOf q) (487)) (countLit q [247, 248]) (countLit q [249, 250]) (count487 q) 1 (meaning483 q) (meaning487 q) hs
  change valuationOf q 483 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 483 = false ∨ valuation q 487 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 483 = false ∨ valuationOf q 485 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [247, 248]) + (countLit q [249, 250]) := List.countP_append (p := literal q) (l₁ := [247, 248]) (l₂ := [249, 250])
  have hm := merge_two (literal (valuationOf q) (483)) (literal (valuationOf q) (485)) (literal (valuationOf q) (488)) (countLit q [247, 248]) (countLit q [249, 250]) (count487 q) 1 1 (meaning483 q) (meaning485 q) (meaning488 q) hs
  change valuationOf q 483 = false ∨ valuationOf q 485 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 483 = false ∨ valuation q 485 = false ∨ valuation q 488 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 489 = true := by
  have hs : count489 q = (countLit q [251]) + (countLit q [252]) := List.countP_append (p := literal q) (l₁ := [251]) (l₂ := [252])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (489)) (countLit q [251]) (countLit q [252]) (count489 q) 1 (meaning251 q) (meaning489 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 489 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 491 = true := by
  have hs : count491 q = (countLit q [253]) + (countLit q [254]) := List.countP_append (p := literal q) (l₁ := [253]) (l₂ := [254])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (491)) (countLit q [253]) (countLit q [254]) (count491 q) 1 (meaning253 q) (meaning491 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 491 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 491 = false ∨ valuationOf q 493 = true := by
  have hs : count493 q = (countLit q [251, 252]) + (countLit q [253, 254]) := List.countP_append (p := literal q) (l₁ := [251, 252]) (l₂ := [253, 254])
  have hm := merge_right (literal (valuationOf q) (491)) (literal (valuationOf q) (493)) (countLit q [251, 252]) (countLit q [253, 254]) (count493 q) 1 (meaning491 q) (meaning493 q) hs
  change valuationOf q 491 = false ∨ valuationOf q 493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 491 = false ∨ valuation q 493 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 489 = false ∨ valuationOf q 493 = true := by
  have hs : count493 q = (countLit q [251, 252]) + (countLit q [253, 254]) := List.countP_append (p := literal q) (l₁ := [251, 252]) (l₂ := [253, 254])
  have hm := merge_left (literal (valuationOf q) (489)) (literal (valuationOf q) (493)) (countLit q [251, 252]) (countLit q [253, 254]) (count493 q) 1 (meaning489 q) (meaning493 q) hs
  change valuationOf q 489 = false ∨ valuationOf q 493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 489 = false ∨ valuation q 493 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 493 = false ∨ valuationOf q 495 = true := by
  have hs : count495 q = (countLit q [247, 248, 249, 250]) + (countLit q [251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [247, 248, 249, 250]) (l₂ := [251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (493)) (literal (valuationOf q) (495)) (countLit q [247, 248, 249, 250]) (countLit q [251, 252, 253, 254]) (count495 q) 1 (meaning493 q) (meaning495 q) hs
  change valuationOf q 493 = false ∨ valuationOf q 495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 493 = false ∨ valuation q 495 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 495 = true := by
  have hs : count495 q = (countLit q [247, 248, 249, 250]) + (countLit q [251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [247, 248, 249, 250]) (l₂ := [251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (487)) (literal (valuationOf q) (495)) (countLit q [247, 248, 249, 250]) (countLit q [251, 252, 253, 254]) (count495 q) 1 (meaning487 q) (meaning495 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 495 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 493 = false ∨ valuationOf q 496 = true := by
  have hs : count495 q = (countLit q [247, 248, 249, 250]) + (countLit q [251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [247, 248, 249, 250]) (l₂ := [251, 252, 253, 254])
  have hm := merge_two (literal (valuationOf q) (487)) (literal (valuationOf q) (493)) (literal (valuationOf q) (496)) (countLit q [247, 248, 249, 250]) (countLit q [251, 252, 253, 254]) (count495 q) 1 1 (meaning487 q) (meaning493 q) (meaning496 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 493 = false ∨ valuationOf q 496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 493 = false ∨ valuation q 496 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 488 = false ∨ valuationOf q 496 = true := by
  have hs : count495 q = (countLit q [247, 248, 249, 250]) + (countLit q [251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [247, 248, 249, 250]) (l₂ := [251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (488)) (literal (valuationOf q) (496)) (countLit q [247, 248, 249, 250]) (countLit q [251, 252, 253, 254]) (count495 q) 2 (meaning488 q) (meaning496 q) hs
  change valuationOf q 488 = false ∨ valuationOf q 496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 488 = false ∨ valuation q 496 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 495 = false ∨ valuationOf q 497 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (495)) (literal (valuationOf q) (497)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 1 (meaning495 q) (meaning497 q) hs
  change valuationOf q 495 = false ∨ valuationOf q 497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 495 = false ∨ valuation q 497 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 496 = false ∨ valuationOf q 498 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (496)) (literal (valuationOf q) (498)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 2 (meaning496 q) (meaning498 q) hs
  change valuationOf q 496 = false ∨ valuationOf q 498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 496 = false ∨ valuation q 498 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 497 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (481)) (literal (valuationOf q) (497)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 1 (meaning481 q) (meaning497 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 497 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 495 = false ∨ valuationOf q 498 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_two (literal (valuationOf q) (481)) (literal (valuationOf q) (495)) (literal (valuationOf q) (498)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 1 1 (meaning481 q) (meaning495 q) (meaning498 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 495 = false ∨ valuationOf q 498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 495 = false ∨ valuation q 498 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 482 = false ∨ valuationOf q 498 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (482)) (literal (valuationOf q) (498)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 2 (meaning482 q) (meaning498 q) hs
  change valuationOf q 482 = false ∨ valuationOf q 498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 482 = false ∨ valuation q 498 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 497 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (497)) (literal (valuationOf q) (499)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 1 (meaning497 q) (meaning499 q) hs
  change valuationOf q 497 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 497 = false ∨ valuation q 499 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 498 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (498)) (literal (valuationOf q) (500)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 2 (meaning498 q) (meaning500 q) hs
  change valuationOf q 498 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 498 = false ∨ valuation q 500 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (467)) (literal (valuationOf q) (499)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 1 (meaning467 q) (meaning499 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 499 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 497 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_two (literal (valuationOf q) (467)) (literal (valuationOf q) (497)) (literal (valuationOf q) (500)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 1 1 (meaning467 q) (meaning497 q) (meaning500 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 497 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 497 = false ∨ valuation q 500 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 468 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (468)) (literal (valuationOf q) (500)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 2 (meaning468 q) (meaning500 q) hs
  change valuationOf q 468 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 468 = false ∨ valuation q 500 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 499 = false ∨ valuationOf q 501 = true := by
  have hs : count501 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (499)) (literal (valuationOf q) (501)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count501 q) 1 (meaning499 q) (meaning501 q) hs
  change valuationOf q 499 = false ∨ valuationOf q 501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 499 = false ∨ valuation q 501 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E256.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112256
