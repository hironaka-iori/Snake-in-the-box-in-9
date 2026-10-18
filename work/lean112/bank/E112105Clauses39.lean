import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 470 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (470)) (literal (valuationOf q) (486)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 2 (meaning470 q) (meaning486 q) hs
  change valuationOf q 470 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 470 = false ∨ valuation q 486 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 485 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (485)) (literal (valuationOf q) (487)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 1 (meaning485 q) (meaning487 q) hs
  change valuationOf q 485 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 485 = false ∨ valuation q 487 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 486 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (486)) (literal (valuationOf q) (488)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 2 (meaning486 q) (meaning488 q) hs
  change valuationOf q 486 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 486 = false ∨ valuation q 488 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (455)) (literal (valuationOf q) (487)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 1 (meaning455 q) (meaning487 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 487 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 485 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (455)) (literal (valuationOf q) (485)) (literal (valuationOf q) (488)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 1 1 (meaning455 q) (meaning485 q) (meaning488 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 485 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 485 = false ∨ valuation q 488 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 456 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (456)) (literal (valuationOf q) (488)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 2 (meaning456 q) (meaning488 q) hs
  change valuationOf q 456 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 456 = false ∨ valuation q 488 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 489 = true := by
  have hs : count489 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (487)) (literal (valuationOf q) (489)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 1 (meaning487 q) (meaning489 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 489 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 488 = false ∨ valuationOf q 490 = true := by
  have hs : count489 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (488)) (literal (valuationOf q) (490)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 2 (meaning488 q) (meaning490 q) hs
  change valuationOf q 488 = false ∨ valuationOf q 490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 488 = false ∨ valuation q 490 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 489 = true := by
  have hs : count489 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (427)) (literal (valuationOf q) (489)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 1 (meaning427 q) (meaning489 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 489 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 487 = false ∨ valuationOf q 490 = true := by
  have hs : count489 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (427)) (literal (valuationOf q) (487)) (literal (valuationOf q) (490)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 1 1 (meaning427 q) (meaning487 q) (meaning490 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 487 = false ∨ valuationOf q 490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 487 = false ∨ valuation q 490 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 428 = false ∨ valuationOf q 490 = true := by
  have hs : count489 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (428)) (literal (valuationOf q) (490)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 2 (meaning428 q) (meaning490 q) hs
  change valuationOf q 428 = false ∨ valuationOf q 490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 428 = false ∨ valuation q 490 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 490 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (490)) (literal (valuationOf q) (492)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count491 q) 2 (meaning490 q) (meaning492 q) hs
  change valuationOf q 490 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 490 = false ∨ valuation q 492 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 489 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (367)) (literal (valuationOf q) (489)) (literal (valuationOf q) (492)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count491 q) 1 1 (meaning367 q) (meaning489 q) (meaning492 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 489 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 489 = false ∨ valuation q 492 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 368 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (368)) (literal (valuationOf q) (492)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count491 q) 2 (meaning368 q) (meaning492 q) hs
  change valuationOf q 368 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 368 = false ∨ valuation q 492 = true := counterClause1262 (baseVal q)

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 492 = false := by
  rw [value492]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count491 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 211 = true ∨ valuation q 212 = true ∨ valuation q 213 = true ∨ valuation q 214 = true ∨ valuation q 215 = true ∨ valuation q 216 = true ∨ valuation q 217 = true ∨ valuation q 218 = true ∨ valuation q 219 = true ∨ valuation q 220 = true ∨ valuation q 221 = true ∨ valuation q 222 = true ∨ valuation q 223 = true ∨ valuation q 224 = true ∨ valuation q 225 = true ∨ valuation q 226 = true ∨ valuation q 227 = true ∨ valuation q 228 = true ∨ valuation q 229 = true ∨ valuation q 230 = true ∨ valuation q 231 = true ∨ valuation q 232 = true ∨ valuation q 233 = true ∨ valuation q 234 = true ∨ valuation q 235 = true ∨ valuation q 236 = true ∨ valuation q 237 = true ∨ valuation q 238 = true ∨ valuation q 239 = true ∨ valuation q 240 = true ∨ valuation q 241 = true ∨ valuation q 242 = true ∨ valuation q 243 = true ∨ valuation q 244 = true ∨ valuation q 245 = true ∨ valuation q 246 = true ∨ valuation q 247 = true ∨ valuation q 248 = true := by
  rw [value125, value126, value127, value128, value129, value130, value131, value132, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value211, value212, value213, value214, value215, value216, value217, value218, value219, value220, value221, value222, value223, value224, value225, value226, value227, value228, value229, value230, value231, value232, value233, value234, value235, value236, value237, value238, value239, value240, value241, value242, value243, value244, value245, value246, value247, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1513 = true := by
  have hs : count1513 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (1513)) (countLit q [-4]) (countLit q [-6]) (count1513 q) 1 (meaningNeg6 q) (meaning1513 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1513 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1513 = true := by
  have hs : count1513 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1513)) (countLit q [-4]) (countLit q [-6]) (count1513 q) 1 (meaningNeg4 q) (meaning1513 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1513 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 6 = true ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-6)) (literal (valuationOf q) (1514)) (countLit q [-4]) (countLit q [-6]) (count1513 q) 1 1 (meaningNeg4 q) (meaningNeg6 q) (meaning1514 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 6)) = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 6 = true ∨ valuation q 1514 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1515 = true := by
  have hs : count1515 q = (countLit q [-2]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -6])
  have hm := merge_right (literal (valuationOf q) (1513)) (literal (valuationOf q) (1515)) (countLit q [-2]) (countLit q [-4, -6]) (count1515 q) 1 (meaning1513 q) (meaning1515 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1515 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1516 = true := by
  have hs : count1515 q = (countLit q [-2]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -6])
  have hm := merge_right (literal (valuationOf q) (1514)) (literal (valuationOf q) (1516)) (countLit q [-2]) (countLit q [-4, -6]) (count1515 q) 2 (meaning1514 q) (meaning1516 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1516 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1515 = true := by
  have hs : count1515 q = (countLit q [-2]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -6])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1515)) (countLit q [-2]) (countLit q [-4, -6]) (count1515 q) 1 (meaningNeg2 q) (meaning1515 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1515 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1513 = false ∨ valuationOf q 1516 = true := by
  have hs : count1515 q = (countLit q [-2]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -6])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1516)) (countLit q [-2]) (countLit q [-4, -6]) (count1515 q) 1 1 (meaningNeg2 q) (meaning1513 q) (meaning1516 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1513 = false ∨ valuation q 1516 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1514 = false ∨ valuationOf q 1517 = true := by
  have hs : count1515 q = (countLit q [-2]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -6])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1517)) (countLit q [-2]) (countLit q [-4, -6]) (count1515 q) 1 2 (meaningNeg2 q) (meaning1514 q) (meaning1517 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1514 = false ∨ valuation q 1517 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-7]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-7)) (literal (valuationOf q) (1518)) (countLit q [-7]) (countLit q [-10]) (count1518 q) 1 (meaningNeg7 q) (meaning1518 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1518 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1520 = true := by
  have hs : count1520 q = (countLit q [-13]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-16])
  have hm := merge_right (literal (valuationOf q) (-16)) (literal (valuationOf q) (1520)) (countLit q [-13]) (countLit q [-16]) (count1520 q) 1 (meaningNeg16 q) (meaning1520 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1520 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1520 = true := by
  have hs : count1520 q = (countLit q [-13]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-16])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1520)) (countLit q [-13]) (countLit q [-16]) (count1520 q) 1 (meaningNeg13 q) (meaning1520 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1520 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 16 = true ∨ valuationOf q 1521 = true := by
  have hs : count1520 q = (countLit q [-13]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-16])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-16)) (literal (valuationOf q) (1521)) (countLit q [-13]) (countLit q [-16]) (count1520 q) 1 1 (meaningNeg13 q) (meaningNeg16 q) (meaning1521 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 16)) = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 1521 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1522 = true := by
  have hs : count1522 q = (countLit q [-7, -10]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-7, -10]) (l₂ := [-13, -16])
  have hm := merge_right (literal (valuationOf q) (1520)) (literal (valuationOf q) (1522)) (countLit q [-7, -10]) (countLit q [-13, -16]) (count1522 q) 1 (meaning1520 q) (meaning1522 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1522 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1523 = true := by
  have hs : count1522 q = (countLit q [-7, -10]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-7, -10]) (l₂ := [-13, -16])
  have hm := merge_right (literal (valuationOf q) (1521)) (literal (valuationOf q) (1523)) (countLit q [-7, -10]) (countLit q [-13, -16]) (count1522 q) 2 (meaning1521 q) (meaning1523 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1523 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1522 = true := by
  have hs : count1522 q = (countLit q [-7, -10]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-7, -10]) (l₂ := [-13, -16])
  have hm := merge_left (literal (valuationOf q) (1518)) (literal (valuationOf q) (1522)) (countLit q [-7, -10]) (countLit q [-13, -16]) (count1522 q) 1 (meaning1518 q) (meaning1522 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1522 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1523 = true := by
  have hs : count1522 q = (countLit q [-7, -10]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-7, -10]) (l₂ := [-13, -16])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1523)) (countLit q [-7, -10]) (countLit q [-13, -16]) (count1522 q) 1 1 (meaning1518 q) (meaning1520 q) (meaning1523 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1520 = false ∨ valuation q 1523 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E105.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112105
