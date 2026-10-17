import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [222, 223, 224, 225, 226, 227, 228, 229]) + (countLit q [230, 231, 232, 233, 234, 235, 236, 237]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228, 229]) (l₂ := [230, 231, 232, 233, 234, 235, 236, 237])
  have hm := merge_two (literal (valuationOf q) (451)) (literal (valuationOf q) (465)) (literal (valuationOf q) (468)) (countLit q [222, 223, 224, 225, 226, 227, 228, 229]) (countLit q [230, 231, 232, 233, 234, 235, 236, 237]) (count467 q) 1 1 (meaning451 q) (meaning465 q) (meaning468 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 465 = false ∨ valuation q 468 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 452 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [222, 223, 224, 225, 226, 227, 228, 229]) + (countLit q [230, 231, 232, 233, 234, 235, 236, 237]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228, 229]) (l₂ := [230, 231, 232, 233, 234, 235, 236, 237])
  have hm := merge_left (literal (valuationOf q) (452)) (literal (valuationOf q) (468)) (countLit q [222, 223, 224, 225, 226, 227, 228, 229]) (countLit q [230, 231, 232, 233, 234, 235, 236, 237]) (count467 q) 2 (meaning452 q) (meaning468 q) hs
  change valuationOf q 452 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 452 = false ∨ valuation q 468 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [238]) + (countLit q [239]) := List.countP_append (p := literal q) (l₁ := [238]) (l₂ := [239])
  have hm := merge_left (literal (valuationOf q) (238)) (literal (valuationOf q) (469)) (countLit q [238]) (countLit q [239]) (count469 q) 1 (meaning238 q) (meaning469 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 469 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [238, 239]) + (countLit q [240, 241]) := List.countP_append (p := literal q) (l₁ := [238, 239]) (l₂ := [240, 241])
  have hm := merge_left (literal (valuationOf q) (469)) (literal (valuationOf q) (473)) (countLit q [238, 239]) (countLit q [240, 241]) (count473 q) 1 (meaning469 q) (meaning473 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 473 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [242]) + (countLit q [243]) := List.countP_append (p := literal q) (l₁ := [242]) (l₂ := [243])
  have hm := merge_right (literal (valuationOf q) (243)) (literal (valuationOf q) (475)) (countLit q [242]) (countLit q [243]) (count475 q) 1 (meaning243 q) (meaning475 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 475 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 242 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [242]) + (countLit q [243]) := List.countP_append (p := literal q) (l₁ := [242]) (l₂ := [243])
  have hm := merge_left (literal (valuationOf q) (242)) (literal (valuationOf q) (475)) (countLit q [242]) (countLit q [243]) (count475 q) 1 (meaning242 q) (meaning475 q) hs
  change valuationOf q 242 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 475 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 242 = false ∨ valuationOf q 243 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [242]) + (countLit q [243]) := List.countP_append (p := literal q) (l₁ := [242]) (l₂ := [243])
  have hm := merge_two (literal (valuationOf q) (242)) (literal (valuationOf q) (243)) (literal (valuationOf q) (476)) (countLit q [242]) (countLit q [243]) (count475 q) 1 1 (meaning242 q) (meaning243 q) (meaning476 q) hs
  change valuationOf q 242 = false ∨ valuationOf q 243 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 243 = false ∨ valuation q 476 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [244]) + (countLit q [245]) := List.countP_append (p := literal q) (l₁ := [244]) (l₂ := [245])
  have hm := merge_left (literal (valuationOf q) (244)) (literal (valuationOf q) (477)) (countLit q [244]) (countLit q [245]) (count477 q) 1 (meaning244 q) (meaning477 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 477 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [242, 243]) + (countLit q [244, 245]) := List.countP_append (p := literal q) (l₁ := [242, 243]) (l₂ := [244, 245])
  have hm := merge_right (literal (valuationOf q) (477)) (literal (valuationOf q) (479)) (countLit q [242, 243]) (countLit q [244, 245]) (count479 q) 1 (meaning477 q) (meaning479 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 479 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [242, 243]) + (countLit q [244, 245]) := List.countP_append (p := literal q) (l₁ := [242, 243]) (l₂ := [244, 245])
  have hm := merge_left (literal (valuationOf q) (475)) (literal (valuationOf q) (479)) (countLit q [242, 243]) (countLit q [244, 245]) (count479 q) 1 (meaning475 q) (meaning479 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 479 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 476 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [242, 243]) + (countLit q [244, 245]) := List.countP_append (p := literal q) (l₁ := [242, 243]) (l₂ := [244, 245])
  have hm := merge_left (literal (valuationOf q) (476)) (literal (valuationOf q) (480)) (countLit q [242, 243]) (countLit q [244, 245]) (count479 q) 2 (meaning476 q) (meaning480 q) hs
  change valuationOf q 476 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 476 = false ∨ valuation q 480 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 479 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [238, 239, 240, 241]) + (countLit q [242, 243, 244, 245]) := List.countP_append (p := literal q) (l₁ := [238, 239, 240, 241]) (l₂ := [242, 243, 244, 245])
  have hm := merge_right (literal (valuationOf q) (479)) (literal (valuationOf q) (481)) (countLit q [238, 239, 240, 241]) (countLit q [242, 243, 244, 245]) (count481 q) 1 (meaning479 q) (meaning481 q) hs
  change valuationOf q 479 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 479 = false ∨ valuation q 481 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 480 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [238, 239, 240, 241]) + (countLit q [242, 243, 244, 245]) := List.countP_append (p := literal q) (l₁ := [238, 239, 240, 241]) (l₂ := [242, 243, 244, 245])
  have hm := merge_right (literal (valuationOf q) (480)) (literal (valuationOf q) (482)) (countLit q [238, 239, 240, 241]) (countLit q [242, 243, 244, 245]) (count481 q) 2 (meaning480 q) (meaning482 q) hs
  change valuationOf q 480 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 480 = false ∨ valuation q 482 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [238, 239, 240, 241]) + (countLit q [242, 243, 244, 245]) := List.countP_append (p := literal q) (l₁ := [238, 239, 240, 241]) (l₂ := [242, 243, 244, 245])
  have hm := merge_left (literal (valuationOf q) (473)) (literal (valuationOf q) (481)) (countLit q [238, 239, 240, 241]) (countLit q [242, 243, 244, 245]) (count481 q) 1 (meaning473 q) (meaning481 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 481 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [238, 239, 240, 241]) + (countLit q [242, 243, 244, 245]) := List.countP_append (p := literal q) (l₁ := [238, 239, 240, 241]) (l₂ := [242, 243, 244, 245])
  have hm := merge_two (literal (valuationOf q) (473)) (literal (valuationOf q) (479)) (literal (valuationOf q) (482)) (countLit q [238, 239, 240, 241]) (countLit q [242, 243, 244, 245]) (count481 q) 1 1 (meaning473 q) (meaning479 q) (meaning482 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 479 = false ∨ valuation q 482 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [246]) + (countLit q [247]) := List.countP_append (p := literal q) (l₁ := [246]) (l₂ := [247])
  have hm := merge_right (literal (valuationOf q) (247)) (literal (valuationOf q) (483)) (countLit q [246]) (countLit q [247]) (count483 q) 1 (meaning247 q) (meaning483 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 483 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 246 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [246]) + (countLit q [247]) := List.countP_append (p := literal q) (l₁ := [246]) (l₂ := [247])
  have hm := merge_left (literal (valuationOf q) (246)) (literal (valuationOf q) (483)) (countLit q [246]) (countLit q [247]) (count483 q) 1 (meaning246 q) (meaning483 q) hs
  change valuationOf q 246 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 483 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [248]) + (countLit q [249]) := List.countP_append (p := literal q) (l₁ := [248]) (l₂ := [249])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (485)) (countLit q [248]) (countLit q [249]) (count485 q) 1 (meaning249 q) (meaning485 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 485 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 485 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [246, 247]) + (countLit q [248, 249]) := List.countP_append (p := literal q) (l₁ := [246, 247]) (l₂ := [248, 249])
  have hm := merge_right (literal (valuationOf q) (485)) (literal (valuationOf q) (487)) (countLit q [246, 247]) (countLit q [248, 249]) (count487 q) 1 (meaning485 q) (meaning487 q) hs
  change valuationOf q 485 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 485 = false ∨ valuation q 487 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 483 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [246, 247]) + (countLit q [248, 249]) := List.countP_append (p := literal q) (l₁ := [246, 247]) (l₂ := [248, 249])
  have hm := merge_left (literal (valuationOf q) (483)) (literal (valuationOf q) (487)) (countLit q [246, 247]) (countLit q [248, 249]) (count487 q) 1 (meaning483 q) (meaning487 q) hs
  change valuationOf q 483 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 483 = false ∨ valuation q 487 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 489 = true := by
  have hs : count489 q = (countLit q [250]) + (countLit q [251]) := List.countP_append (p := literal q) (l₁ := [250]) (l₂ := [251])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (489)) (countLit q [250]) (countLit q [251]) (count489 q) 1 (meaning251 q) (meaning489 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 489 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 491 = true := by
  have hs : count491 q = (countLit q [252]) + (countLit q [253]) := List.countP_append (p := literal q) (l₁ := [252]) (l₂ := [253])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (491)) (countLit q [252]) (countLit q [253]) (count491 q) 1 (meaning253 q) (meaning491 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 491 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 491 = false ∨ valuationOf q 493 = true := by
  have hs : count493 q = (countLit q [250, 251]) + (countLit q [252, 253]) := List.countP_append (p := literal q) (l₁ := [250, 251]) (l₂ := [252, 253])
  have hm := merge_right (literal (valuationOf q) (491)) (literal (valuationOf q) (493)) (countLit q [250, 251]) (countLit q [252, 253]) (count493 q) 1 (meaning491 q) (meaning493 q) hs
  change valuationOf q 491 = false ∨ valuationOf q 493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 491 = false ∨ valuation q 493 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 489 = false ∨ valuationOf q 493 = true := by
  have hs : count493 q = (countLit q [250, 251]) + (countLit q [252, 253]) := List.countP_append (p := literal q) (l₁ := [250, 251]) (l₂ := [252, 253])
  have hm := merge_left (literal (valuationOf q) (489)) (literal (valuationOf q) (493)) (countLit q [250, 251]) (countLit q [252, 253]) (count493 q) 1 (meaning489 q) (meaning493 q) hs
  change valuationOf q 489 = false ∨ valuationOf q 493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 489 = false ∨ valuation q 493 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 493 = false ∨ valuationOf q 495 = true := by
  have hs : count495 q = (countLit q [246, 247, 248, 249]) + (countLit q [250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [246, 247, 248, 249]) (l₂ := [250, 251, 252, 253])
  have hm := merge_right (literal (valuationOf q) (493)) (literal (valuationOf q) (495)) (countLit q [246, 247, 248, 249]) (countLit q [250, 251, 252, 253]) (count495 q) 1 (meaning493 q) (meaning495 q) hs
  change valuationOf q 493 = false ∨ valuationOf q 495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 493 = false ∨ valuation q 495 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 495 = true := by
  have hs : count495 q = (countLit q [246, 247, 248, 249]) + (countLit q [250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [246, 247, 248, 249]) (l₂ := [250, 251, 252, 253])
  have hm := merge_left (literal (valuationOf q) (487)) (literal (valuationOf q) (495)) (countLit q [246, 247, 248, 249]) (countLit q [250, 251, 252, 253]) (count495 q) 1 (meaning487 q) (meaning495 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 495 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 493 = false ∨ valuationOf q 496 = true := by
  have hs : count495 q = (countLit q [246, 247, 248, 249]) + (countLit q [250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [246, 247, 248, 249]) (l₂ := [250, 251, 252, 253])
  have hm := merge_two (literal (valuationOf q) (487)) (literal (valuationOf q) (493)) (literal (valuationOf q) (496)) (countLit q [246, 247, 248, 249]) (countLit q [250, 251, 252, 253]) (count495 q) 1 1 (meaning487 q) (meaning493 q) (meaning496 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 493 = false ∨ valuationOf q 496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 493 = false ∨ valuation q 496 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 495 = false ∨ valuationOf q 497 = true := by
  have hs : count497 q = (countLit q [238, 239, 240, 241, 242, 243, 244, 245]) + (countLit q [246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [238, 239, 240, 241, 242, 243, 244, 245]) (l₂ := [246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_right (literal (valuationOf q) (495)) (literal (valuationOf q) (497)) (countLit q [238, 239, 240, 241, 242, 243, 244, 245]) (countLit q [246, 247, 248, 249, 250, 251, 252, 253]) (count497 q) 1 (meaning495 q) (meaning497 q) hs
  change valuationOf q 495 = false ∨ valuationOf q 497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 495 = false ∨ valuation q 497 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 496 = false ∨ valuationOf q 498 = true := by
  have hs : count497 q = (countLit q [238, 239, 240, 241, 242, 243, 244, 245]) + (countLit q [246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [238, 239, 240, 241, 242, 243, 244, 245]) (l₂ := [246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_right (literal (valuationOf q) (496)) (literal (valuationOf q) (498)) (countLit q [238, 239, 240, 241, 242, 243, 244, 245]) (countLit q [246, 247, 248, 249, 250, 251, 252, 253]) (count497 q) 2 (meaning496 q) (meaning498 q) hs
  change valuationOf q 496 = false ∨ valuationOf q 498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 496 = false ∨ valuation q 498 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 497 = true := by
  have hs : count497 q = (countLit q [238, 239, 240, 241, 242, 243, 244, 245]) + (countLit q [246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [238, 239, 240, 241, 242, 243, 244, 245]) (l₂ := [246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_left (literal (valuationOf q) (481)) (literal (valuationOf q) (497)) (countLit q [238, 239, 240, 241, 242, 243, 244, 245]) (countLit q [246, 247, 248, 249, 250, 251, 252, 253]) (count497 q) 1 (meaning481 q) (meaning497 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 497 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 495 = false ∨ valuationOf q 498 = true := by
  have hs : count497 q = (countLit q [238, 239, 240, 241, 242, 243, 244, 245]) + (countLit q [246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [238, 239, 240, 241, 242, 243, 244, 245]) (l₂ := [246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_two (literal (valuationOf q) (481)) (literal (valuationOf q) (495)) (literal (valuationOf q) (498)) (countLit q [238, 239, 240, 241, 242, 243, 244, 245]) (countLit q [246, 247, 248, 249, 250, 251, 252, 253]) (count497 q) 1 1 (meaning481 q) (meaning495 q) (meaning498 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 495 = false ∨ valuationOf q 498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 495 = false ∨ valuation q 498 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 482 = false ∨ valuationOf q 498 = true := by
  have hs : count497 q = (countLit q [238, 239, 240, 241, 242, 243, 244, 245]) + (countLit q [246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [238, 239, 240, 241, 242, 243, 244, 245]) (l₂ := [246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_left (literal (valuationOf q) (482)) (literal (valuationOf q) (498)) (countLit q [238, 239, 240, 241, 242, 243, 244, 245]) (countLit q [246, 247, 248, 249, 250, 251, 252, 253]) (count497 q) 2 (meaning482 q) (meaning498 q) hs
  change valuationOf q 482 = false ∨ valuationOf q 498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 482 = false ∨ valuation q 498 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E057.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112057
