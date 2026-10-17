import E112147Semantics
import B112E147Inputs
namespace Snake9.Regrowth.E112147
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [194, 195, 196]) + (countLit q [197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196]) (l₂ := [197, 198, 199, 200])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (387)) (countLit q [194, 195, 196]) (countLit q [197, 198, 199, 200]) (count387 q) 1 (meaning379 q) (meaning387 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 387 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200])
  have hm := merge_right (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (countLit q [188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200]) (count389 q) 1 (meaning387 q) (meaning389 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200])
  have hm := merge_left (literal (valuationOf q) (375)) (literal (valuationOf q) (389)) (countLit q [188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200]) (count389 q) 1 (meaning375 q) (meaning389 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 389 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]) + (countLit q [188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]) (l₂ := [188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]) (countLit q [188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]) + (countLit q [188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]) (l₂ := [188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (391)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]) (countLit q [188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) (count391 q) 1 (meaning365 q) (meaning391 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 391 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200])
  have hm := merge_left (literal (valuationOf q) (343)) (literal (valuationOf q) (393)) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) (count393 q) 1 (meaning343 q) (meaning393 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 393 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 391 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200])
  have hm := merge_two (literal (valuationOf q) (343)) (literal (valuationOf q) (391)) (literal (valuationOf q) (394)) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) (count393 q) 1 1 (meaning343 q) (meaning391 q) (meaning394 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 391 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 391 = false ∨ valuation q 394 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 344 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200])
  have hm := merge_left (literal (valuationOf q) (344)) (literal (valuationOf q) (394)) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) (count393 q) 2 (meaning344 q) (meaning394 q) hs
  change valuationOf q 344 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 344 = false ∨ valuation q 394 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 394 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200])
  have hm := merge_right (literal (valuationOf q) (394)) (literal (valuationOf q) (396)) (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) (count395 q) 2 (meaning394 q) (meaning396 q) hs
  change valuationOf q 394 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 394 = false ∨ valuation q 396 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 393 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200])
  have hm := merge_two (literal (valuationOf q) (295)) (literal (valuationOf q) (393)) (literal (valuationOf q) (396)) (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) (count395 q) 1 1 (meaning295 q) (meaning393 q) (meaning396 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 393 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 393 = false ∨ valuation q 396 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 296 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200])
  have hm := merge_left (literal (valuationOf q) (296)) (literal (valuationOf q) (396)) (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]) (count395 q) 2 (meaning296 q) (meaning396 q) hs
  change valuationOf q 296 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 296 = false ∨ valuation q 396 = true := counterClause300 (baseVal q)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 396 = false := by
  rw [value396]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count395 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause302 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 6 = true ∨ valuationOf q 670 = true := by
  have hs : count669 q = (countLit q [-3]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-6)) (literal (valuationOf q) (670)) (countLit q [-3]) (countLit q [-6]) (count669 q) 1 1 (meaningNeg3 q) (meaningNeg6 q) (meaning670 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 6)) = false ∨ valuationOf q 670 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 6 = true ∨ valuation q 670 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 671 = true := by
  have hs : count671 q = (countLit q [-1]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -6])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (671)) (countLit q [-1]) (countLit q [-3, -6]) (count671 q) 1 (meaningNeg1 q) (meaning671 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 671 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 671 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 670 = false ∨ valuationOf q 673 = true := by
  have hs : count671 q = (countLit q [-1]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -6])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (670)) (literal (valuationOf q) (673)) (countLit q [-1]) (countLit q [-3, -6]) (count671 q) 1 2 (meaningNeg1 q) (meaning670 q) (meaning673 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 670 = false ∨ valuationOf q 673 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 670 = false ∨ valuation q 673 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 674 = true := by
  have hs : count674 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (674)) (countLit q [-9]) (countLit q [-11]) (count674 q) 1 (meaningNeg11 q) (meaning674 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 674 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 674 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 674 = true := by
  have hs : count674 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (674)) (countLit q [-9]) (countLit q [-11]) (count674 q) 1 (meaningNeg9 q) (meaning674 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 674 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 674 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 11 = true ∨ valuationOf q 675 = true := by
  have hs : count674 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-11)) (literal (valuationOf q) (675)) (countLit q [-9]) (countLit q [-11]) (count674 q) 1 1 (meaningNeg9 q) (meaningNeg11 q) (meaning675 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 11)) = false ∨ valuationOf q 675 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 11 = true ∨ valuation q 675 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 676 = true := by
  have hs : count676 q = (countLit q [-7]) + (countLit q [-9, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-9, -11])
  have hm := merge_left (literal (valuationOf q) (-7)) (literal (valuationOf q) (676)) (countLit q [-7]) (countLit q [-9, -11]) (count676 q) 1 (meaningNeg7 q) (meaning676 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 676 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 676 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 674 = false ∨ valuationOf q 677 = true := by
  have hs : count676 q = (countLit q [-7]) + (countLit q [-9, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-9, -11])
  have hm := merge_two (literal (valuationOf q) (-7)) (literal (valuationOf q) (674)) (literal (valuationOf q) (677)) (countLit q [-7]) (countLit q [-9, -11]) (count676 q) 1 1 (meaningNeg7 q) (meaning674 q) (meaning677 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 674 = false ∨ valuationOf q 677 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 674 = false ∨ valuation q 677 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 675 = false ∨ valuationOf q 678 = true := by
  have hs : count676 q = (countLit q [-7]) + (countLit q [-9, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-9, -11])
  have hm := merge_two (literal (valuationOf q) (-7)) (literal (valuationOf q) (675)) (literal (valuationOf q) (678)) (countLit q [-7]) (countLit q [-9, -11]) (count676 q) 1 2 (meaningNeg7 q) (meaning675 q) (meaning678 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 675 = false ∨ valuationOf q 678 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 675 = false ∨ valuation q 678 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 676 = false ∨ valuationOf q 679 = true := by
  have hs : count679 q = (countLit q [-1, -3, -6]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-7, -9, -11])
  have hm := merge_right (literal (valuationOf q) (676)) (literal (valuationOf q) (679)) (countLit q [-1, -3, -6]) (countLit q [-7, -9, -11]) (count679 q) 1 (meaning676 q) (meaning679 q) hs
  change valuationOf q 676 = false ∨ valuationOf q 679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 676 = false ∨ valuation q 679 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 677 = false ∨ valuationOf q 680 = true := by
  have hs : count679 q = (countLit q [-1, -3, -6]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-7, -9, -11])
  have hm := merge_right (literal (valuationOf q) (677)) (literal (valuationOf q) (680)) (countLit q [-1, -3, -6]) (countLit q [-7, -9, -11]) (count679 q) 2 (meaning677 q) (meaning680 q) hs
  change valuationOf q 677 = false ∨ valuationOf q 680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 677 = false ∨ valuation q 680 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 678 = false ∨ valuationOf q 681 = true := by
  have hs : count679 q = (countLit q [-1, -3, -6]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-7, -9, -11])
  have hm := merge_right (literal (valuationOf q) (678)) (literal (valuationOf q) (681)) (countLit q [-1, -3, -6]) (countLit q [-7, -9, -11]) (count679 q) 3 (meaning678 q) (meaning681 q) hs
  change valuationOf q 678 = false ∨ valuationOf q 681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 678 = false ∨ valuation q 681 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 671 = false ∨ valuationOf q 676 = false ∨ valuationOf q 680 = true := by
  have hs : count679 q = (countLit q [-1, -3, -6]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-7, -9, -11])
  have hm := merge_two (literal (valuationOf q) (671)) (literal (valuationOf q) (676)) (literal (valuationOf q) (680)) (countLit q [-1, -3, -6]) (countLit q [-7, -9, -11]) (count679 q) 1 1 (meaning671 q) (meaning676 q) (meaning680 q) hs
  change valuationOf q 671 = false ∨ valuationOf q 676 = false ∨ valuationOf q 680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 671 = false ∨ valuation q 676 = false ∨ valuation q 680 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 671 = false ∨ valuationOf q 677 = false ∨ valuationOf q 681 = true := by
  have hs : count679 q = (countLit q [-1, -3, -6]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-7, -9, -11])
  have hm := merge_two (literal (valuationOf q) (671)) (literal (valuationOf q) (677)) (literal (valuationOf q) (681)) (countLit q [-1, -3, -6]) (countLit q [-7, -9, -11]) (count679 q) 1 2 (meaning671 q) (meaning677 q) (meaning681 q) hs
  change valuationOf q 671 = false ∨ valuationOf q 677 = false ∨ valuationOf q 681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 671 = false ∨ valuation q 677 = false ∨ valuation q 681 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 671 = false ∨ valuationOf q 678 = false ∨ valuationOf q 682 = true := by
  have hs : count679 q = (countLit q [-1, -3, -6]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-7, -9, -11])
  have hm := merge_two (literal (valuationOf q) (671)) (literal (valuationOf q) (678)) (literal (valuationOf q) (682)) (countLit q [-1, -3, -6]) (countLit q [-7, -9, -11]) (count679 q) 1 3 (meaning671 q) (meaning678 q) (meaning682 q) hs
  change valuationOf q 671 = false ∨ valuationOf q 678 = false ∨ valuationOf q 682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 671 = false ∨ valuation q 678 = false ∨ valuation q 682 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 673 = false ∨ valuationOf q 681 = true := by
  have hs : count679 q = (countLit q [-1, -3, -6]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-7, -9, -11])
  have hm := merge_left (literal (valuationOf q) (673)) (literal (valuationOf q) (681)) (countLit q [-1, -3, -6]) (countLit q [-7, -9, -11]) (count679 q) 3 (meaning673 q) (meaning681 q) hs
  change valuationOf q 673 = false ∨ valuationOf q 681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 673 = false ∨ valuation q 681 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 673 = false ∨ valuationOf q 676 = false ∨ valuationOf q 682 = true := by
  have hs : count679 q = (countLit q [-1, -3, -6]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-7, -9, -11])
  have hm := merge_two (literal (valuationOf q) (673)) (literal (valuationOf q) (676)) (literal (valuationOf q) (682)) (countLit q [-1, -3, -6]) (countLit q [-7, -9, -11]) (count679 q) 3 1 (meaning673 q) (meaning676 q) (meaning682 q) hs
  change valuationOf q 673 = false ∨ valuationOf q 676 = false ∨ valuationOf q 682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 673 = false ∨ valuation q 676 = false ∨ valuation q 682 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 673 = false ∨ valuationOf q 677 = false ∨ valuationOf q 683 = true := by
  have hs : count679 q = (countLit q [-1, -3, -6]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-7, -9, -11])
  have hm := merge_two (literal (valuationOf q) (673)) (literal (valuationOf q) (677)) (literal (valuationOf q) (683)) (countLit q [-1, -3, -6]) (countLit q [-7, -9, -11]) (count679 q) 3 2 (meaning673 q) (meaning677 q) (meaning683 q) hs
  change valuationOf q 673 = false ∨ valuationOf q 677 = false ∨ valuationOf q 683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 673 = false ∨ valuation q 677 = false ∨ valuation q 683 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 685 = true := by
  have hs : count685 q = (countLit q [-14]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (685)) (countLit q [-14]) (countLit q [-18]) (count685 q) 1 (meaningNeg18 q) (meaning685 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 685 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 685 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E147.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112147
