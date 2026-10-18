import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 454 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (454)) (literal (valuationOf q) (456)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 2 (meaning454 q) (meaning456 q) hs
  change valuationOf q 454 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 454 = false ∨ valuation q 456 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (439)) (literal (valuationOf q) (455)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 (meaning439 q) (meaning455 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 455 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (439)) (literal (valuationOf q) (453)) (literal (valuationOf q) (456)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 1 (meaning439 q) (meaning453 q) (meaning456 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 453 = false ∨ valuation q 456 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 440 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (440)) (literal (valuationOf q) (456)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 2 (meaning440 q) (meaning456 q) hs
  change valuationOf q 440 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 440 = false ∨ valuation q 456 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_right (literal (valuationOf q) (234)) (literal (valuationOf q) (457)) (countLit q [233]) (countLit q [234]) (count457 q) 1 (meaning234 q) (meaning457 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 457 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_left (literal (valuationOf q) (457)) (literal (valuationOf q) (461)) (countLit q [233, 234]) (countLit q [235, 236]) (count461 q) 1 (meaning457 q) (meaning461 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 461 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [237]) + (countLit q [238]) := List.countP_append (p := literal q) (l₁ := [237]) (l₂ := [238])
  have hm := merge_left (literal (valuationOf q) (237)) (literal (valuationOf q) (463)) (countLit q [237]) (countLit q [238]) (count463 q) 1 (meaning237 q) (meaning463 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 463 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 240 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [239]) + (countLit q [240]) := List.countP_append (p := literal q) (l₁ := [239]) (l₂ := [240])
  have hm := merge_right (literal (valuationOf q) (240)) (literal (valuationOf q) (465)) (countLit q [239]) (countLit q [240]) (count465 q) 1 (meaning240 q) (meaning465 q) hs
  change valuationOf q 240 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 465 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [239]) + (countLit q [240]) := List.countP_append (p := literal q) (l₁ := [239]) (l₂ := [240])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (465)) (countLit q [239]) (countLit q [240]) (count465 q) 1 (meaning239 q) (meaning465 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 465 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 240 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [239]) + (countLit q [240]) := List.countP_append (p := literal q) (l₁ := [239]) (l₂ := [240])
  have hm := merge_two (literal (valuationOf q) (239)) (literal (valuationOf q) (240)) (literal (valuationOf q) (466)) (countLit q [239]) (countLit q [240]) (count465 q) 1 1 (meaning239 q) (meaning240 q) (meaning466 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 240 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 240 = false ∨ valuation q 466 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_right (literal (valuationOf q) (465)) (literal (valuationOf q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning465 q) (meaning467 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 467 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 466 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_right (literal (valuationOf q) (466)) (literal (valuationOf q) (468)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 2 (meaning466 q) (meaning468 q) hs
  change valuationOf q 466 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 466 = false ∨ valuation q 468 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_left (literal (valuationOf q) (463)) (literal (valuationOf q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning463 q) (meaning467 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 467 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (467)) (literal (valuationOf q) (469)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 1 (meaning467 q) (meaning469 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 469 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 468 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (468)) (literal (valuationOf q) (470)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 2 (meaning468 q) (meaning470 q) hs
  change valuationOf q 468 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 468 = false ∨ valuation q 470 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (461)) (literal (valuationOf q) (469)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 1 (meaning461 q) (meaning469 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 469 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 467 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_two (literal (valuationOf q) (461)) (literal (valuationOf q) (467)) (literal (valuationOf q) (470)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 1 1 (meaning461 q) (meaning467 q) (meaning470 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 467 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 467 = false ∨ valuation q 470 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [241]) + (countLit q [242]) := List.countP_append (p := literal q) (l₁ := [241]) (l₂ := [242])
  have hm := merge_left (literal (valuationOf q) (241)) (literal (valuationOf q) (471)) (countLit q [241]) (countLit q [242]) (count471 q) 1 (meaning241 q) (meaning471 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 471 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [241, 242]) + (countLit q [243, 244]) := List.countP_append (p := literal q) (l₁ := [241, 242]) (l₂ := [243, 244])
  have hm := merge_left (literal (valuationOf q) (471)) (literal (valuationOf q) (475)) (countLit q [241, 242]) (countLit q [243, 244]) (count475 q) 1 (meaning471 q) (meaning475 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 475 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 246 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [245]) + (countLit q [246]) := List.countP_append (p := literal q) (l₁ := [245]) (l₂ := [246])
  have hm := merge_right (literal (valuationOf q) (246)) (literal (valuationOf q) (477)) (countLit q [245]) (countLit q [246]) (count477 q) 1 (meaning246 q) (meaning477 q) hs
  change valuationOf q 246 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 477 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [247]) + (countLit q [248]) := List.countP_append (p := literal q) (l₁ := [247]) (l₂ := [248])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (479)) (countLit q [247]) (countLit q [248]) (count479 q) 1 (meaning247 q) (meaning479 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 479 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 479 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [245, 246]) + (countLit q [247, 248]) := List.countP_append (p := literal q) (l₁ := [245, 246]) (l₂ := [247, 248])
  have hm := merge_right (literal (valuationOf q) (479)) (literal (valuationOf q) (481)) (countLit q [245, 246]) (countLit q [247, 248]) (count481 q) 1 (meaning479 q) (meaning481 q) hs
  change valuationOf q 479 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 479 = false ∨ valuation q 481 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [245, 246]) + (countLit q [247, 248]) := List.countP_append (p := literal q) (l₁ := [245, 246]) (l₂ := [247, 248])
  have hm := merge_left (literal (valuationOf q) (477)) (literal (valuationOf q) (481)) (countLit q [245, 246]) (countLit q [247, 248]) (count481 q) 1 (meaning477 q) (meaning481 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 481 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [245, 246]) + (countLit q [247, 248]) := List.countP_append (p := literal q) (l₁ := [245, 246]) (l₂ := [247, 248])
  have hm := merge_two (literal (valuationOf q) (477)) (literal (valuationOf q) (479)) (literal (valuationOf q) (482)) (countLit q [245, 246]) (countLit q [247, 248]) (count481 q) 1 1 (meaning477 q) (meaning479 q) (meaning482 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 479 = false ∨ valuation q 482 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (481)) (literal (valuationOf q) (483)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count483 q) 1 (meaning481 q) (meaning483 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 483 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 482 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (482)) (literal (valuationOf q) (484)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count483 q) 2 (meaning482 q) (meaning484 q) hs
  change valuationOf q 482 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 482 = false ∨ valuation q 484 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (475)) (literal (valuationOf q) (483)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count483 q) 1 (meaning475 q) (meaning483 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 483 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 481 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (475)) (literal (valuationOf q) (481)) (literal (valuationOf q) (484)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count483 q) 1 1 (meaning475 q) (meaning481 q) (meaning484 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 481 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 481 = false ∨ valuation q 484 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 483 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (483)) (literal (valuationOf q) (485)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 1 (meaning483 q) (meaning485 q) hs
  change valuationOf q 483 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 483 = false ∨ valuation q 485 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 484 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (484)) (literal (valuationOf q) (486)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 2 (meaning484 q) (meaning486 q) hs
  change valuationOf q 484 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 484 = false ∨ valuation q 486 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (469)) (literal (valuationOf q) (485)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 1 (meaning469 q) (meaning485 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 485 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 483 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (469)) (literal (valuationOf q) (483)) (literal (valuationOf q) (486)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 1 1 (meaning469 q) (meaning483 q) (meaning486 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 483 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 483 = false ∨ valuation q 486 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E105.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112105
