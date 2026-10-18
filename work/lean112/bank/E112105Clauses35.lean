import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 366 = false ∨ valuationOf q 368 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_right (literal (valuationOf q) (366)) (literal (valuationOf q) (368)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 2 (meaning366 q) (meaning368 q) hs
  change valuationOf q 366 = false ∨ valuationOf q 368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 366 = false ∨ valuation q 368 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_left (literal (valuationOf q) (305)) (literal (valuationOf q) (367)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 1 (meaning305 q) (meaning367 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 367 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 365 = false ∨ valuationOf q 368 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_two (literal (valuationOf q) (305)) (literal (valuationOf q) (365)) (literal (valuationOf q) (368)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 1 1 (meaning305 q) (meaning365 q) (meaning368 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 365 = false ∨ valuationOf q 368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 365 = false ∨ valuation q 368 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 306 = false ∨ valuationOf q 368 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_left (literal (valuationOf q) (306)) (literal (valuationOf q) (368)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 2 (meaning306 q) (meaning368 q) hs
  change valuationOf q 306 = false ∨ valuationOf q 368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 306 = false ∨ valuation q 368 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [188]) + (countLit q [189]) := List.countP_append (p := literal q) (l₁ := [188]) (l₂ := [189])
  have hm := merge_left (literal (valuationOf q) (188)) (literal (valuationOf q) (369)) (countLit q [188]) (countLit q [189]) (count369 q) 1 (meaning188 q) (meaning369 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 369 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [187]) + (countLit q [188, 189]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188, 189])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [187]) (countLit q [188, 189]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 190 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [190]) + (countLit q [191]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191])
  have hm := merge_left (literal (valuationOf q) (190)) (literal (valuationOf q) (373)) (countLit q [190]) (countLit q [191]) (count373 q) 1 (meaning190 q) (meaning373 q) hs
  change valuationOf q 190 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 373 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 192 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [192]) + (countLit q [193]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193])
  have hm := merge_left (literal (valuationOf q) (192)) (literal (valuationOf q) (375)) (countLit q [192]) (countLit q [193]) (count375 q) 1 (meaning192 q) (meaning375 q) hs
  change valuationOf q 192 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 375 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [190, 191]) + (countLit q [192, 193]) := List.countP_append (p := literal q) (l₁ := [190, 191]) (l₂ := [192, 193])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [190, 191]) (countLit q [192, 193]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [190, 191]) + (countLit q [192, 193]) := List.countP_append (p := literal q) (l₁ := [190, 191]) (l₂ := [192, 193])
  have hm := merge_left (literal (valuationOf q) (373)) (literal (valuationOf q) (377)) (countLit q [190, 191]) (countLit q [192, 193]) (count377 q) 1 (meaning373 q) (meaning377 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 377 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [190, 191]) + (countLit q [192, 193]) := List.countP_append (p := literal q) (l₁ := [190, 191]) (l₂ := [192, 193])
  have hm := merge_two (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (literal (valuationOf q) (378)) (countLit q [190, 191]) (countLit q [192, 193]) (count377 q) 1 1 (meaning373 q) (meaning375 q) (meaning378 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = false ∨ valuation q 378 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [187, 188, 189]) + (countLit q [190, 191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189]) (l₂ := [190, 191, 192, 193])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [187, 188, 189]) (countLit q [190, 191, 192, 193]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [187, 188, 189]) + (countLit q [190, 191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189]) (l₂ := [190, 191, 192, 193])
  have hm := merge_right (literal (valuationOf q) (378)) (literal (valuationOf q) (380)) (countLit q [187, 188, 189]) (countLit q [190, 191, 192, 193]) (count379 q) 2 (meaning378 q) (meaning380 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 380 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [187, 188, 189]) + (countLit q [190, 191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189]) (l₂ := [190, 191, 192, 193])
  have hm := merge_left (literal (valuationOf q) (371)) (literal (valuationOf q) (379)) (countLit q [187, 188, 189]) (countLit q [190, 191, 192, 193]) (count379 q) 1 (meaning371 q) (meaning379 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 379 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 377 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [187, 188, 189]) + (countLit q [190, 191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189]) (l₂ := [190, 191, 192, 193])
  have hm := merge_two (literal (valuationOf q) (371)) (literal (valuationOf q) (377)) (literal (valuationOf q) (380)) (countLit q [187, 188, 189]) (countLit q [190, 191, 192, 193]) (count379 q) 1 1 (meaning371 q) (meaning377 q) (meaning380 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 377 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 377 = false ∨ valuation q 380 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 195 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_right (literal (valuationOf q) (195)) (literal (valuationOf q) (381)) (countLit q [194]) (countLit q [195]) (count381 q) 1 (meaning195 q) (meaning381 q) hs
  change valuationOf q 195 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 381 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_left (literal (valuationOf q) (196)) (literal (valuationOf q) (383)) (countLit q [196]) (countLit q [197]) (count383 q) 1 (meaning196 q) (meaning383 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 383 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [194, 195]) + (countLit q [196, 197]) := List.countP_append (p := literal q) (l₁ := [194, 195]) (l₂ := [196, 197])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [194, 195]) (countLit q [196, 197]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [194, 195]) + (countLit q [196, 197]) := List.countP_append (p := literal q) (l₁ := [194, 195]) (l₂ := [196, 197])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (385)) (countLit q [194, 195]) (countLit q [196, 197]) (count385 q) 1 (meaning381 q) (meaning385 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 385 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 198 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [198]) + (countLit q [199]) := List.countP_append (p := literal q) (l₁ := [198]) (l₂ := [199])
  have hm := merge_left (literal (valuationOf q) (198)) (literal (valuationOf q) (387)) (countLit q [198]) (countLit q [199]) (count387 q) 1 (meaning198 q) (meaning387 q) hs
  change valuationOf q 198 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 387 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_left (literal (valuationOf q) (200)) (literal (valuationOf q) (389)) (countLit q [200]) (countLit q [201]) (count389 q) 1 (meaning200 q) (meaning389 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 389 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [198, 199]) (countLit q [200, 201]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (391)) (countLit q [198, 199]) (countLit q [200, 201]) (count391 q) 1 (meaning387 q) (meaning391 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 391 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_two (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (literal (valuationOf q) (392)) (countLit q [198, 199]) (countLit q [200, 201]) (count391 q) 1 1 (meaning387 q) (meaning389 q) (meaning392 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = false ∨ valuation q 392 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [194, 195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [194, 195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 392 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [194, 195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (392)) (literal (valuationOf q) (394)) (countLit q [194, 195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 2 (meaning392 q) (meaning394 q) hs
  change valuationOf q 392 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 392 = false ∨ valuation q 394 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [194, 195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_left (literal (valuationOf q) (385)) (literal (valuationOf q) (393)) (countLit q [194, 195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 1 (meaning385 q) (meaning393 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 393 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 391 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [194, 195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_two (literal (valuationOf q) (385)) (literal (valuationOf q) (391)) (literal (valuationOf q) (394)) (countLit q [194, 195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 1 1 (meaning385 q) (meaning391 q) (meaning394 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 391 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 391 = false ∨ valuation q 394 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 394 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (394)) (literal (valuationOf q) (396)) (countLit q [187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) (count395 q) 2 (meaning394 q) (meaning396 q) hs
  change valuationOf q 394 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 394 = false ∨ valuation q 396 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (395)) (countLit q [187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) (count395 q) 1 (meaning379 q) (meaning395 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 395 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E105.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112105
