import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 446 = false ∨ valuationOf q 454 = true := by
  have hs : count453 q = (countLit q [225, 226, 227, 228]) + (countLit q [229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228]) (l₂ := [229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (446)) (literal (valuationOf q) (454)) (countLit q [225, 226, 227, 228]) (countLit q [229, 230, 231, 232]) (count453 q) 2 (meaning446 q) (meaning454 q) hs
  change valuationOf q 446 = false ∨ valuationOf q 454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 446 = false ∨ valuation q 454 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 454 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (454)) (literal (valuationOf q) (456)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 2 (meaning454 q) (meaning456 q) hs
  change valuationOf q 454 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 454 = false ∨ valuation q 456 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (439)) (literal (valuationOf q) (455)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 (meaning439 q) (meaning455 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 455 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_two (literal (valuationOf q) (439)) (literal (valuationOf q) (453)) (literal (valuationOf q) (456)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 1 1 (meaning439 q) (meaning453 q) (meaning456 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 453 = false ∨ valuation q 456 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 440 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (440)) (literal (valuationOf q) (456)) (countLit q [218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232]) (count455 q) 2 (meaning440 q) (meaning456 q) hs
  change valuationOf q 440 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 440 = false ∨ valuation q 456 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [235]) + (countLit q [236]) := List.countP_append (p := literal q) (l₁ := [235]) (l₂ := [236])
  have hm := merge_left (literal (valuationOf q) (235)) (literal (valuationOf q) (459)) (countLit q [235]) (countLit q [236]) (count459 q) 1 (meaning235 q) (meaning459 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 459 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_right (literal (valuationOf q) (459)) (literal (valuationOf q) (461)) (countLit q [233, 234]) (countLit q [235, 236]) (count461 q) 1 (meaning459 q) (meaning461 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 461 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [237]) + (countLit q [238]) := List.countP_append (p := literal q) (l₁ := [237]) (l₂ := [238])
  have hm := merge_left (literal (valuationOf q) (237)) (literal (valuationOf q) (463)) (countLit q [237]) (countLit q [238]) (count463 q) 1 (meaning237 q) (meaning463 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 463 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [239]) + (countLit q [240]) := List.countP_append (p := literal q) (l₁ := [239]) (l₂ := [240])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (465)) (countLit q [239]) (countLit q [240]) (count465 q) 1 (meaning239 q) (meaning465 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 465 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_right (literal (valuationOf q) (465)) (literal (valuationOf q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning465 q) (meaning467 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 467 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_left (literal (valuationOf q) (463)) (literal (valuationOf q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning463 q) (meaning467 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 467 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_two (literal (valuationOf q) (463)) (literal (valuationOf q) (465)) (literal (valuationOf q) (468)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 1 (meaning463 q) (meaning465 q) (meaning468 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 465 = false ∨ valuation q 468 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (467)) (literal (valuationOf q) (469)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 1 (meaning467 q) (meaning469 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 469 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 468 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (468)) (literal (valuationOf q) (470)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 2 (meaning468 q) (meaning470 q) hs
  change valuationOf q 468 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 468 = false ∨ valuation q 470 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (461)) (literal (valuationOf q) (469)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 1 (meaning461 q) (meaning469 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 469 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 467 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_two (literal (valuationOf q) (461)) (literal (valuationOf q) (467)) (literal (valuationOf q) (470)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count469 q) 1 1 (meaning461 q) (meaning467 q) (meaning470 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 467 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 467 = false ∨ valuation q 470 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [241]) + (countLit q [242]) := List.countP_append (p := literal q) (l₁ := [241]) (l₂ := [242])
  have hm := merge_left (literal (valuationOf q) (241)) (literal (valuationOf q) (471)) (countLit q [241]) (countLit q [242]) (count471 q) 1 (meaning241 q) (meaning471 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 471 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [243]) + (countLit q [244]) := List.countP_append (p := literal q) (l₁ := [243]) (l₂ := [244])
  have hm := merge_right (literal (valuationOf q) (244)) (literal (valuationOf q) (473)) (countLit q [243]) (countLit q [244]) (count473 q) 1 (meaning244 q) (meaning473 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 473 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [243]) + (countLit q [244]) := List.countP_append (p := literal q) (l₁ := [243]) (l₂ := [244])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (473)) (countLit q [243]) (countLit q [244]) (count473 q) 1 (meaning243 q) (meaning473 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 473 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 244 = false ∨ valuationOf q 474 = true := by
  have hs : count473 q = (countLit q [243]) + (countLit q [244]) := List.countP_append (p := literal q) (l₁ := [243]) (l₂ := [244])
  have hm := merge_two (literal (valuationOf q) (243)) (literal (valuationOf q) (244)) (literal (valuationOf q) (474)) (countLit q [243]) (countLit q [244]) (count473 q) 1 1 (meaning243 q) (meaning244 q) (meaning474 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 244 = false ∨ valuationOf q 474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 244 = false ∨ valuation q 474 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [241, 242]) + (countLit q [243, 244]) := List.countP_append (p := literal q) (l₁ := [241, 242]) (l₂ := [243, 244])
  have hm := merge_right (literal (valuationOf q) (473)) (literal (valuationOf q) (475)) (countLit q [241, 242]) (countLit q [243, 244]) (count475 q) 1 (meaning473 q) (meaning475 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 475 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 474 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [241, 242]) + (countLit q [243, 244]) := List.countP_append (p := literal q) (l₁ := [241, 242]) (l₂ := [243, 244])
  have hm := merge_right (literal (valuationOf q) (474)) (literal (valuationOf q) (476)) (countLit q [241, 242]) (countLit q [243, 244]) (count475 q) 2 (meaning474 q) (meaning476 q) hs
  change valuationOf q 474 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 474 = false ∨ valuation q 476 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 475 = true := by
  have hs : count475 q = (countLit q [241, 242]) + (countLit q [243, 244]) := List.countP_append (p := literal q) (l₁ := [241, 242]) (l₂ := [243, 244])
  have hm := merge_left (literal (valuationOf q) (471)) (literal (valuationOf q) (475)) (countLit q [241, 242]) (countLit q [243, 244]) (count475 q) 1 (meaning471 q) (meaning475 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 475 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [241, 242]) + (countLit q [243, 244]) := List.countP_append (p := literal q) (l₁ := [241, 242]) (l₂ := [243, 244])
  have hm := merge_two (literal (valuationOf q) (471)) (literal (valuationOf q) (473)) (literal (valuationOf q) (476)) (countLit q [241, 242]) (countLit q [243, 244]) (count475 q) 1 1 (meaning471 q) (meaning473 q) (meaning476 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 473 = false ∨ valuation q 476 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 246 = false ∨ valuationOf q 477 = true := by
  have hs : count477 q = (countLit q [245]) + (countLit q [246]) := List.countP_append (p := literal q) (l₁ := [245]) (l₂ := [246])
  have hm := merge_right (literal (valuationOf q) (246)) (literal (valuationOf q) (477)) (countLit q [245]) (countLit q [246]) (count477 q) 1 (meaning246 q) (meaning477 q) hs
  change valuationOf q 246 = false ∨ valuationOf q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 477 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [247]) + (countLit q [248]) := List.countP_append (p := literal q) (l₁ := [247]) (l₂ := [248])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (479)) (countLit q [247]) (countLit q [248]) (count479 q) 1 (meaning247 q) (meaning479 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 479 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 479 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [245, 246]) + (countLit q [247, 248]) := List.countP_append (p := literal q) (l₁ := [245, 246]) (l₂ := [247, 248])
  have hm := merge_right (literal (valuationOf q) (479)) (literal (valuationOf q) (481)) (countLit q [245, 246]) (countLit q [247, 248]) (count481 q) 1 (meaning479 q) (meaning481 q) hs
  change valuationOf q 479 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 479 = false ∨ valuation q 481 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [245, 246]) + (countLit q [247, 248]) := List.countP_append (p := literal q) (l₁ := [245, 246]) (l₂ := [247, 248])
  have hm := merge_left (literal (valuationOf q) (477)) (literal (valuationOf q) (481)) (countLit q [245, 246]) (countLit q [247, 248]) (count481 q) 1 (meaning477 q) (meaning481 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 481 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [245, 246]) + (countLit q [247, 248]) := List.countP_append (p := literal q) (l₁ := [245, 246]) (l₂ := [247, 248])
  have hm := merge_two (literal (valuationOf q) (477)) (literal (valuationOf q) (479)) (literal (valuationOf q) (482)) (countLit q [245, 246]) (countLit q [247, 248]) (count481 q) 1 1 (meaning477 q) (meaning479 q) (meaning482 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 479 = false ∨ valuation q 482 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (481)) (literal (valuationOf q) (483)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count483 q) 1 (meaning481 q) (meaning483 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 483 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 482 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (482)) (literal (valuationOf q) (484)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count483 q) 2 (meaning482 q) (meaning484 q) hs
  change valuationOf q 482 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 482 = false ∨ valuation q 484 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E089.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112089
