import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (475)) (literal (valuationOf q) (483)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count483 q) 1 (meaning475 q) (meaning483 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 483 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 481 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (475)) (literal (valuationOf q) (481)) (literal (valuationOf q) (484)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count483 q) 1 1 (meaning475 q) (meaning481 q) (meaning484 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 481 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 481 = false ∨ valuation q 484 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 476 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (476)) (literal (valuationOf q) (484)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count483 q) 2 (meaning476 q) (meaning484 q) hs
  change valuationOf q 476 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 476 = false ∨ valuation q 484 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 483 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (483)) (literal (valuationOf q) (485)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 1 (meaning483 q) (meaning485 q) hs
  change valuationOf q 483 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 483 = false ∨ valuation q 485 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 484 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (484)) (literal (valuationOf q) (486)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 2 (meaning484 q) (meaning486 q) hs
  change valuationOf q 484 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 484 = false ∨ valuation q 486 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (469)) (literal (valuationOf q) (485)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 1 (meaning469 q) (meaning485 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 485 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 483 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (469)) (literal (valuationOf q) (483)) (literal (valuationOf q) (486)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 1 1 (meaning469 q) (meaning483 q) (meaning486 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 483 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 483 = false ∨ valuation q 486 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 470 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (470)) (literal (valuationOf q) (486)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 2 (meaning470 q) (meaning486 q) hs
  change valuationOf q 470 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 470 = false ∨ valuation q 486 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 485 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (485)) (literal (valuationOf q) (487)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 1 (meaning485 q) (meaning487 q) hs
  change valuationOf q 485 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 485 = false ∨ valuation q 487 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 486 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (486)) (literal (valuationOf q) (488)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 2 (meaning486 q) (meaning488 q) hs
  change valuationOf q 486 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 486 = false ∨ valuation q 488 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (455)) (literal (valuationOf q) (487)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 1 (meaning455 q) (meaning487 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 487 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 485 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (455)) (literal (valuationOf q) (485)) (literal (valuationOf q) (488)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 1 1 (meaning455 q) (meaning485 q) (meaning488 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 485 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 485 = false ∨ valuation q 488 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 456 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (456)) (literal (valuationOf q) (488)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 2 (meaning456 q) (meaning488 q) hs
  change valuationOf q 456 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 456 = false ∨ valuation q 488 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 489 = true := by
  have hs : count489 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (487)) (literal (valuationOf q) (489)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 1 (meaning487 q) (meaning489 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 489 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 488 = false ∨ valuationOf q 490 = true := by
  have hs : count489 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (488)) (literal (valuationOf q) (490)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 2 (meaning488 q) (meaning490 q) hs
  change valuationOf q 488 = false ∨ valuationOf q 490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 488 = false ∨ valuation q 490 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 489 = true := by
  have hs : count489 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (427)) (literal (valuationOf q) (489)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 1 (meaning427 q) (meaning489 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 489 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 487 = false ∨ valuationOf q 490 = true := by
  have hs : count489 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (427)) (literal (valuationOf q) (487)) (literal (valuationOf q) (490)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 1 1 (meaning427 q) (meaning487 q) (meaning490 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 487 = false ∨ valuationOf q 490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 487 = false ∨ valuation q 490 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 428 = false ∨ valuationOf q 490 = true := by
  have hs : count489 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (428)) (literal (valuationOf q) (490)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 2 (meaning428 q) (meaning490 q) hs
  change valuationOf q 428 = false ∨ valuationOf q 490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 428 = false ∨ valuation q 490 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 490 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (490)) (literal (valuationOf q) (492)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count491 q) 2 (meaning490 q) (meaning492 q) hs
  change valuationOf q 490 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 490 = false ∨ valuation q 492 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 489 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (367)) (literal (valuationOf q) (489)) (literal (valuationOf q) (492)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count491 q) 1 1 (meaning367 q) (meaning489 q) (meaning492 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 489 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 489 = false ∨ valuation q 492 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 368 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (368)) (literal (valuationOf q) (492)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count491 q) 2 (meaning368 q) (meaning492 q) hs
  change valuationOf q 368 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 368 = false ∨ valuation q 492 = true := counterClause1301 (baseVal q)

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 492 = false := by
  rw [value492]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count491 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 211 = true ∨ valuation q 213 = true ∨ valuation q 214 = true ∨ valuation q 215 = true ∨ valuation q 216 = true ∨ valuation q 217 = true ∨ valuation q 218 = true ∨ valuation q 219 = true ∨ valuation q 220 = true ∨ valuation q 221 = true ∨ valuation q 222 = true ∨ valuation q 223 = true ∨ valuation q 224 = true ∨ valuation q 225 = true ∨ valuation q 226 = true ∨ valuation q 227 = true ∨ valuation q 228 = true ∨ valuation q 229 = true ∨ valuation q 230 = true ∨ valuation q 231 = true ∨ valuation q 232 = true ∨ valuation q 233 = true ∨ valuation q 234 = true ∨ valuation q 235 = true ∨ valuation q 236 = true ∨ valuation q 237 = true ∨ valuation q 238 = true ∨ valuation q 239 = true ∨ valuation q 240 = true ∨ valuation q 241 = true ∨ valuation q 242 = true ∨ valuation q 243 = true ∨ valuation q 244 = true ∨ valuation q 245 = true ∨ valuation q 246 = true ∨ valuation q 247 = true ∨ valuation q 248 = true := by
  rw [value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value211, value213, value214, value215, value216, value217, value218, value219, value220, value221, value222, value223, value224, value225, value226, value227, value228, value229, value230, value231, value232, value233, value234, value235, value236, value237, value238, value239, value240, value241, value242, value243, value244, value245, value246, value247, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-5]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-8])
  have hm := merge_right (literal (valuationOf q) (-8)) (literal (valuationOf q) (1505)) (countLit q [-5]) (countLit q [-8]) (count1505 q) 1 (meaningNeg8 q) (meaning1505 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1505 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-5]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-8])
  have hm := merge_left (literal (valuationOf q) (-5)) (literal (valuationOf q) (1505)) (countLit q [-5]) (countLit q [-8]) (count1505 q) 1 (meaningNeg5 q) (meaning1505 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1505 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 8 = true ∨ valuationOf q 1506 = true := by
  have hs : count1505 q = (countLit q [-5]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-8])
  have hm := merge_two (literal (valuationOf q) (-5)) (literal (valuationOf q) (-8)) (literal (valuationOf q) (1506)) (countLit q [-5]) (countLit q [-8]) (count1505 q) 1 1 (meaningNeg5 q) (meaningNeg8 q) (meaning1506 q) hs
  change (! (valuationOf q 5)) = false ∨ (! (valuationOf q 8)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 1506 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-2]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -8])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (countLit q [-2]) (countLit q [-5, -8]) (count1507 q) 1 (meaning1505 q) (meaning1507 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-2]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -8])
  have hm := merge_right (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (countLit q [-2]) (countLit q [-5, -8]) (count1507 q) 2 (meaning1506 q) (meaning1508 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-2]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -8])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1507)) (countLit q [-2]) (countLit q [-5, -8]) (count1507 q) 1 (meaningNeg2 q) (meaning1507 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1507 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-2]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -8])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1508)) (countLit q [-2]) (countLit q [-5, -8]) (count1507 q) 1 1 (meaningNeg2 q) (meaning1505 q) (meaning1508 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1505 = false ∨ valuation q 1508 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true := by
  have hs : count1507 q = (countLit q [-2]) + (countLit q [-5, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -8])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1509)) (countLit q [-2]) (countLit q [-5, -8]) (count1507 q) 1 2 (meaningNeg2 q) (meaning1506 q) (meaning1509 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1506 = false ∨ valuation q 1509 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (1510)) (countLit q [-9]) (countLit q [-10]) (count1510 q) 1 (meaningNeg10 q) (meaning1510 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1510 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E089.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112089
