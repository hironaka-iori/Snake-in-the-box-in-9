import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 456 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [224, 225, 226, 227, 228, 229, 230, 231]) + (countLit q [232, 233, 234, 235, 236, 237, 238, 239]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227, 228, 229, 230, 231]) (l₂ := [232, 233, 234, 235, 236, 237, 238, 239])
  have hm := merge_left (literal (valuationOf q) (456)) (literal (valuationOf q) (472)) (countLit q [224, 225, 226, 227, 228, 229, 230, 231]) (countLit q [232, 233, 234, 235, 236, 237, 238, 239]) (count471 q) 2 (meaning456 q) (meaning472 q) hs
  change valuationOf q 456 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 456 = false ∨ valuation q 472 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [242]) + (countLit q [243]) := List.countP_append (p := literal q) (l₁ := [242]) (l₂ := [243])
  have hm := merge_right (literal (valuationOf q) (243)) (literal (valuationOf q) (475)) (countLit q [242]) (countLit q [243]) (count475 q) 1 (meaning243 q) (meaning475 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 475 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [240, 241]) + (countLit q [242, 243]) := List.countP_append (p := literal q) (l₁ := [240, 241]) (l₂ := [242, 243])
  have hm := merge_right (literal (valuationOf q) (475)) (literal (valuationOf q) (477)) (countLit q [240, 241]) (countLit q [242, 243]) (count477 q) 1 (meaning475 q) (meaning477 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 477 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [244]) + (countLit q [245]) := List.countP_append (p := literal q) (l₁ := [244]) (l₂ := [245])
  have hm := merge_left (literal (valuationOf q) (244)) (literal (valuationOf q) (479)) (countLit q [244]) (countLit q [245]) (count479 q) 1 (meaning244 q) (meaning479 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 479 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 246 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [246]) + (countLit q [247]) := List.countP_append (p := literal q) (l₁ := [246]) (l₂ := [247])
  have hm := merge_left (literal (valuationOf q) (246)) (literal (valuationOf q) (481)) (countLit q [246]) (countLit q [247]) (count481 q) 1 (meaning246 q) (meaning481 q) hs
  change valuationOf q 246 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 481 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [244, 245]) + (countLit q [246, 247]) := List.countP_append (p := literal q) (l₁ := [244, 245]) (l₂ := [246, 247])
  have hm := merge_right (literal (valuationOf q) (481)) (literal (valuationOf q) (483)) (countLit q [244, 245]) (countLit q [246, 247]) (count483 q) 1 (meaning481 q) (meaning483 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 483 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 479 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [244, 245]) + (countLit q [246, 247]) := List.countP_append (p := literal q) (l₁ := [244, 245]) (l₂ := [246, 247])
  have hm := merge_left (literal (valuationOf q) (479)) (literal (valuationOf q) (483)) (countLit q [244, 245]) (countLit q [246, 247]) (count483 q) 1 (meaning479 q) (meaning483 q) hs
  change valuationOf q 479 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 479 = false ∨ valuation q 483 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 483 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [240, 241, 242, 243]) + (countLit q [244, 245, 246, 247]) := List.countP_append (p := literal q) (l₁ := [240, 241, 242, 243]) (l₂ := [244, 245, 246, 247])
  have hm := merge_right (literal (valuationOf q) (483)) (literal (valuationOf q) (485)) (countLit q [240, 241, 242, 243]) (countLit q [244, 245, 246, 247]) (count485 q) 1 (meaning483 q) (meaning485 q) hs
  change valuationOf q 483 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 483 = false ∨ valuation q 485 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [240, 241, 242, 243]) + (countLit q [244, 245, 246, 247]) := List.countP_append (p := literal q) (l₁ := [240, 241, 242, 243]) (l₂ := [244, 245, 246, 247])
  have hm := merge_left (literal (valuationOf q) (477)) (literal (valuationOf q) (485)) (countLit q [240, 241, 242, 243]) (countLit q [244, 245, 246, 247]) (count485 q) 1 (meaning477 q) (meaning485 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 485 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 483 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [240, 241, 242, 243]) + (countLit q [244, 245, 246, 247]) := List.countP_append (p := literal q) (l₁ := [240, 241, 242, 243]) (l₂ := [244, 245, 246, 247])
  have hm := merge_two (literal (valuationOf q) (477)) (literal (valuationOf q) (483)) (literal (valuationOf q) (486)) (countLit q [240, 241, 242, 243]) (countLit q [244, 245, 246, 247]) (count485 q) 1 1 (meaning477 q) (meaning483 q) (meaning486 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 483 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 483 = false ∨ valuation q 486 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [248]) + (countLit q [249]) := List.countP_append (p := literal q) (l₁ := [248]) (l₂ := [249])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (487)) (countLit q [248]) (countLit q [249]) (count487 q) 1 (meaning249 q) (meaning487 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 487 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 248 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [248]) + (countLit q [249]) := List.countP_append (p := literal q) (l₁ := [248]) (l₂ := [249])
  have hm := merge_left (literal (valuationOf q) (248)) (literal (valuationOf q) (487)) (countLit q [248]) (countLit q [249]) (count487 q) 1 (meaning248 q) (meaning487 q) hs
  change valuationOf q 248 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 487 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 248 = false ∨ valuationOf q 249 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [248]) + (countLit q [249]) := List.countP_append (p := literal q) (l₁ := [248]) (l₂ := [249])
  have hm := merge_two (literal (valuationOf q) (248)) (literal (valuationOf q) (249)) (literal (valuationOf q) (488)) (countLit q [248]) (countLit q [249]) (count487 q) 1 1 (meaning248 q) (meaning249 q) (meaning488 q) hs
  change valuationOf q 248 = false ∨ valuationOf q 249 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 249 = false ∨ valuation q 488 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 489 = true := by
  have hs : count489 q = (countLit q [250]) + (countLit q [251]) := List.countP_append (p := literal q) (l₁ := [250]) (l₂ := [251])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (489)) (countLit q [250]) (countLit q [251]) (count489 q) 1 (meaning251 q) (meaning489 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 489 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 489 = false ∨ valuationOf q 491 = true := by
  have hs : count491 q = (countLit q [248, 249]) + (countLit q [250, 251]) := List.countP_append (p := literal q) (l₁ := [248, 249]) (l₂ := [250, 251])
  have hm := merge_right (literal (valuationOf q) (489)) (literal (valuationOf q) (491)) (countLit q [248, 249]) (countLit q [250, 251]) (count491 q) 1 (meaning489 q) (meaning491 q) hs
  change valuationOf q 489 = false ∨ valuationOf q 491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 489 = false ∨ valuation q 491 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 491 = true := by
  have hs : count491 q = (countLit q [248, 249]) + (countLit q [250, 251]) := List.countP_append (p := literal q) (l₁ := [248, 249]) (l₂ := [250, 251])
  have hm := merge_left (literal (valuationOf q) (487)) (literal (valuationOf q) (491)) (countLit q [248, 249]) (countLit q [250, 251]) (count491 q) 1 (meaning487 q) (meaning491 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 491 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 489 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [248, 249]) + (countLit q [250, 251]) := List.countP_append (p := literal q) (l₁ := [248, 249]) (l₂ := [250, 251])
  have hm := merge_two (literal (valuationOf q) (487)) (literal (valuationOf q) (489)) (literal (valuationOf q) (492)) (countLit q [248, 249]) (countLit q [250, 251]) (count491 q) 1 1 (meaning487 q) (meaning489 q) (meaning492 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 489 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 489 = false ∨ valuation q 492 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 488 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [248, 249]) + (countLit q [250, 251]) := List.countP_append (p := literal q) (l₁ := [248, 249]) (l₂ := [250, 251])
  have hm := merge_left (literal (valuationOf q) (488)) (literal (valuationOf q) (492)) (countLit q [248, 249]) (countLit q [250, 251]) (count491 q) 2 (meaning488 q) (meaning492 q) hs
  change valuationOf q 488 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 488 = false ∨ valuation q 492 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 493 = true := by
  have hs : count493 q = (countLit q [252]) + (countLit q [253]) := List.countP_append (p := literal q) (l₁ := [252]) (l₂ := [253])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (493)) (countLit q [252]) (countLit q [253]) (count493 q) 1 (meaning253 q) (meaning493 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 493 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 495 = true := by
  have hs : count495 q = (countLit q [254]) + (countLit q [255]) := List.countP_append (p := literal q) (l₁ := [254]) (l₂ := [255])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (495)) (countLit q [254]) (countLit q [255]) (count495 q) 1 (meaning255 q) (meaning495 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 495 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 495 = false ∨ valuationOf q 497 = true := by
  have hs : count497 q = (countLit q [252, 253]) + (countLit q [254, 255]) := List.countP_append (p := literal q) (l₁ := [252, 253]) (l₂ := [254, 255])
  have hm := merge_right (literal (valuationOf q) (495)) (literal (valuationOf q) (497)) (countLit q [252, 253]) (countLit q [254, 255]) (count497 q) 1 (meaning495 q) (meaning497 q) hs
  change valuationOf q 495 = false ∨ valuationOf q 497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 495 = false ∨ valuation q 497 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 493 = false ∨ valuationOf q 497 = true := by
  have hs : count497 q = (countLit q [252, 253]) + (countLit q [254, 255]) := List.countP_append (p := literal q) (l₁ := [252, 253]) (l₂ := [254, 255])
  have hm := merge_left (literal (valuationOf q) (493)) (literal (valuationOf q) (497)) (countLit q [252, 253]) (countLit q [254, 255]) (count497 q) 1 (meaning493 q) (meaning497 q) hs
  change valuationOf q 493 = false ∨ valuationOf q 497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 493 = false ∨ valuation q 497 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 493 = false ∨ valuationOf q 495 = false ∨ valuationOf q 498 = true := by
  have hs : count497 q = (countLit q [252, 253]) + (countLit q [254, 255]) := List.countP_append (p := literal q) (l₁ := [252, 253]) (l₂ := [254, 255])
  have hm := merge_two (literal (valuationOf q) (493)) (literal (valuationOf q) (495)) (literal (valuationOf q) (498)) (countLit q [252, 253]) (countLit q [254, 255]) (count497 q) 1 1 (meaning493 q) (meaning495 q) (meaning498 q) hs
  change valuationOf q 493 = false ∨ valuationOf q 495 = false ∨ valuationOf q 498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 493 = false ∨ valuation q 495 = false ∨ valuation q 498 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 497 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [248, 249, 250, 251]) + (countLit q [252, 253, 254, 255]) := List.countP_append (p := literal q) (l₁ := [248, 249, 250, 251]) (l₂ := [252, 253, 254, 255])
  have hm := merge_right (literal (valuationOf q) (497)) (literal (valuationOf q) (499)) (countLit q [248, 249, 250, 251]) (countLit q [252, 253, 254, 255]) (count499 q) 1 (meaning497 q) (meaning499 q) hs
  change valuationOf q 497 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 497 = false ∨ valuation q 499 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 498 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [248, 249, 250, 251]) + (countLit q [252, 253, 254, 255]) := List.countP_append (p := literal q) (l₁ := [248, 249, 250, 251]) (l₂ := [252, 253, 254, 255])
  have hm := merge_right (literal (valuationOf q) (498)) (literal (valuationOf q) (500)) (countLit q [248, 249, 250, 251]) (countLit q [252, 253, 254, 255]) (count499 q) 2 (meaning498 q) (meaning500 q) hs
  change valuationOf q 498 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 498 = false ∨ valuation q 500 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 491 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [248, 249, 250, 251]) + (countLit q [252, 253, 254, 255]) := List.countP_append (p := literal q) (l₁ := [248, 249, 250, 251]) (l₂ := [252, 253, 254, 255])
  have hm := merge_left (literal (valuationOf q) (491)) (literal (valuationOf q) (499)) (countLit q [248, 249, 250, 251]) (countLit q [252, 253, 254, 255]) (count499 q) 1 (meaning491 q) (meaning499 q) hs
  change valuationOf q 491 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 491 = false ∨ valuation q 499 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 491 = false ∨ valuationOf q 497 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [248, 249, 250, 251]) + (countLit q [252, 253, 254, 255]) := List.countP_append (p := literal q) (l₁ := [248, 249, 250, 251]) (l₂ := [252, 253, 254, 255])
  have hm := merge_two (literal (valuationOf q) (491)) (literal (valuationOf q) (497)) (literal (valuationOf q) (500)) (countLit q [248, 249, 250, 251]) (countLit q [252, 253, 254, 255]) (count499 q) 1 1 (meaning491 q) (meaning497 q) (meaning500 q) hs
  change valuationOf q 491 = false ∨ valuationOf q 497 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 491 = false ∨ valuation q 497 = false ∨ valuation q 500 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 492 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [248, 249, 250, 251]) + (countLit q [252, 253, 254, 255]) := List.countP_append (p := literal q) (l₁ := [248, 249, 250, 251]) (l₂ := [252, 253, 254, 255])
  have hm := merge_left (literal (valuationOf q) (492)) (literal (valuationOf q) (500)) (countLit q [248, 249, 250, 251]) (countLit q [252, 253, 254, 255]) (count499 q) 2 (meaning492 q) (meaning500 q) hs
  change valuationOf q 492 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 492 = false ∨ valuation q 500 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 499 = false ∨ valuationOf q 501 = true := by
  have hs : count501 q = (countLit q [240, 241, 242, 243, 244, 245, 246, 247]) + (countLit q [248, 249, 250, 251, 252, 253, 254, 255]) := List.countP_append (p := literal q) (l₁ := [240, 241, 242, 243, 244, 245, 246, 247]) (l₂ := [248, 249, 250, 251, 252, 253, 254, 255])
  have hm := merge_right (literal (valuationOf q) (499)) (literal (valuationOf q) (501)) (countLit q [240, 241, 242, 243, 244, 245, 246, 247]) (countLit q [248, 249, 250, 251, 252, 253, 254, 255]) (count501 q) 1 (meaning499 q) (meaning501 q) hs
  change valuationOf q 499 = false ∨ valuationOf q 501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 499 = false ∨ valuation q 501 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 500 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [240, 241, 242, 243, 244, 245, 246, 247]) + (countLit q [248, 249, 250, 251, 252, 253, 254, 255]) := List.countP_append (p := literal q) (l₁ := [240, 241, 242, 243, 244, 245, 246, 247]) (l₂ := [248, 249, 250, 251, 252, 253, 254, 255])
  have hm := merge_right (literal (valuationOf q) (500)) (literal (valuationOf q) (502)) (countLit q [240, 241, 242, 243, 244, 245, 246, 247]) (countLit q [248, 249, 250, 251, 252, 253, 254, 255]) (count501 q) 2 (meaning500 q) (meaning502 q) hs
  change valuationOf q 500 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 500 = false ∨ valuation q 502 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 485 = false ∨ valuationOf q 501 = true := by
  have hs : count501 q = (countLit q [240, 241, 242, 243, 244, 245, 246, 247]) + (countLit q [248, 249, 250, 251, 252, 253, 254, 255]) := List.countP_append (p := literal q) (l₁ := [240, 241, 242, 243, 244, 245, 246, 247]) (l₂ := [248, 249, 250, 251, 252, 253, 254, 255])
  have hm := merge_left (literal (valuationOf q) (485)) (literal (valuationOf q) (501)) (countLit q [240, 241, 242, 243, 244, 245, 246, 247]) (countLit q [248, 249, 250, 251, 252, 253, 254, 255]) (count501 q) 1 (meaning485 q) (meaning501 q) hs
  change valuationOf q 485 = false ∨ valuationOf q 501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 485 = false ∨ valuation q 501 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 485 = false ∨ valuationOf q 499 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [240, 241, 242, 243, 244, 245, 246, 247]) + (countLit q [248, 249, 250, 251, 252, 253, 254, 255]) := List.countP_append (p := literal q) (l₁ := [240, 241, 242, 243, 244, 245, 246, 247]) (l₂ := [248, 249, 250, 251, 252, 253, 254, 255])
  have hm := merge_two (literal (valuationOf q) (485)) (literal (valuationOf q) (499)) (literal (valuationOf q) (502)) (countLit q [240, 241, 242, 243, 244, 245, 246, 247]) (countLit q [248, 249, 250, 251, 252, 253, 254, 255]) (count501 q) 1 1 (meaning485 q) (meaning499 q) (meaning502 q) hs
  change valuationOf q 485 = false ∨ valuationOf q 499 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 485 = false ∨ valuation q 499 = false ∨ valuation q 502 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E055.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112055
