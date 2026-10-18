import E112148Semantics
import B112E148Inputs
namespace Snake9.Regrowth.E112148
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 438 = false ∨ valuationOf q 440 = true := by
  have hs : count439 q = (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (438)) (literal (valuationOf q) (440)) (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count439 q) 2 (meaning438 q) (meaning440 q) hs
  change valuationOf q 438 = false ∨ valuationOf q 440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 438 = false ∨ valuation q 440 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 437 = false ∨ valuationOf q 440 = true := by
  have hs : count439 q = (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_two (literal (valuationOf q) (329)) (literal (valuationOf q) (437)) (literal (valuationOf q) (440)) (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count439 q) 1 1 (meaning329 q) (meaning437 q) (meaning440 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 437 = false ∨ valuationOf q 440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 437 = false ∨ valuation q 440 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 330 = false ∨ valuationOf q 440 = true := by
  have hs : count439 q = (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (330)) (literal (valuationOf q) (440)) (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count439 q) 2 (meaning330 q) (meaning440 q) hs
  change valuationOf q 330 = false ∨ valuationOf q 440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 330 = false ∨ valuation q 440 = true := counterClause291 (baseVal q)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 440 = false := by
  rw [value440]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count439 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause293 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1327 = true := by
  have hs : count1327 q = (countLit q [-2]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1327)) (countLit q [-2]) (countLit q [-6]) (count1327 q) 1 (meaningNeg2 q) (meaning1327 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1327 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 6 = true ∨ valuationOf q 1328 = true := by
  have hs : count1327 q = (countLit q [-2]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (-6)) (literal (valuationOf q) (1328)) (countLit q [-2]) (countLit q [-6]) (count1327 q) 1 1 (meaningNeg2 q) (meaningNeg6 q) (meaning1328 q) hs
  change (! (valuationOf q 2)) = false ∨ (! (valuationOf q 6)) = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 6 = true ∨ valuation q 1328 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1329 = true := by
  have hs : count1329 q = (countLit q [-1]) + (countLit q [-2, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -6])
  have hm := merge_right (literal (valuationOf q) (1327)) (literal (valuationOf q) (1329)) (countLit q [-1]) (countLit q [-2, -6]) (count1329 q) 1 (meaning1327 q) (meaning1329 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1329 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1330 = true := by
  have hs : count1329 q = (countLit q [-1]) + (countLit q [-2, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -6])
  have hm := merge_right (literal (valuationOf q) (1328)) (literal (valuationOf q) (1330)) (countLit q [-1]) (countLit q [-2, -6]) (count1329 q) 2 (meaning1328 q) (meaning1330 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1330 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 1327 = false ∨ valuationOf q 1330 = true := by
  have hs : count1329 q = (countLit q [-1]) + (countLit q [-2, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -6])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (1327)) (literal (valuationOf q) (1330)) (countLit q [-1]) (countLit q [-2, -6]) (count1329 q) 1 1 (meaningNeg1 q) (meaning1327 q) (meaning1330 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 1327 = false ∨ valuation q 1330 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 1328 = false ∨ valuationOf q 1331 = true := by
  have hs : count1329 q = (countLit q [-1]) + (countLit q [-2, -6]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -6])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (1328)) (literal (valuationOf q) (1331)) (countLit q [-1]) (countLit q [-2, -6]) (count1329 q) 1 2 (meaningNeg1 q) (meaning1328 q) (meaning1331 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 1328 = false ∨ valuation q 1331 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1332 = true := by
  have hs : count1332 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1332)) (countLit q [-12]) (countLit q [-13]) (count1332 q) 1 (meaningNeg13 q) (meaning1332 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1332 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1332 = true := by
  have hs : count1332 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-12)) (literal (valuationOf q) (1332)) (countLit q [-12]) (countLit q [-13]) (count1332 q) 1 (meaningNeg12 q) (meaning1332 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1332 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1333 = true := by
  have hs : count1332 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1333)) (countLit q [-12]) (countLit q [-13]) (count1332 q) 1 1 (meaningNeg12 q) (meaningNeg13 q) (meaning1333 q) hs
  change (! (valuationOf q 12)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 1333 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1334 = true := by
  have hs : count1334 q = (countLit q [-10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1332)) (literal (valuationOf q) (1334)) (countLit q [-10]) (countLit q [-12, -13]) (count1334 q) 1 (meaning1332 q) (meaning1334 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1334 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1335 = true := by
  have hs : count1334 q = (countLit q [-10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1333)) (literal (valuationOf q) (1335)) (countLit q [-10]) (countLit q [-12, -13]) (count1334 q) 2 (meaning1333 q) (meaning1335 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1335 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1334 = true := by
  have hs : count1334 q = (countLit q [-10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12, -13])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1334)) (countLit q [-10]) (countLit q [-12, -13]) (count1334 q) 1 (meaningNeg10 q) (meaning1334 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1334 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1332 = false ∨ valuationOf q 1335 = true := by
  have hs : count1334 q = (countLit q [-10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (1332)) (literal (valuationOf q) (1335)) (countLit q [-10]) (countLit q [-12, -13]) (count1334 q) 1 1 (meaningNeg10 q) (meaning1332 q) (meaning1335 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1332 = false ∨ valuation q 1335 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1333 = false ∨ valuationOf q 1336 = true := by
  have hs : count1334 q = (countLit q [-10]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (1333)) (literal (valuationOf q) (1336)) (countLit q [-10]) (countLit q [-12, -13]) (count1334 q) 1 2 (meaningNeg10 q) (meaning1333 q) (meaning1336 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1333 = false ∨ valuation q 1336 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1338 = true := by
  have hs : count1337 q = (countLit q [-1, -2, -6]) + (countLit q [-10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1334)) (literal (valuationOf q) (1338)) (countLit q [-1, -2, -6]) (countLit q [-10, -12, -13]) (count1337 q) 1 1 (meaning1329 q) (meaning1334 q) (meaning1338 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1334 = false ∨ valuation q 1338 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1335 = false ∨ valuationOf q 1339 = true := by
  have hs : count1337 q = (countLit q [-1, -2, -6]) + (countLit q [-10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1335)) (literal (valuationOf q) (1339)) (countLit q [-1, -2, -6]) (countLit q [-10, -12, -13]) (count1337 q) 1 2 (meaning1329 q) (meaning1335 q) (meaning1339 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1335 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1335 = false ∨ valuation q 1339 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1336 = false ∨ valuationOf q 1340 = true := by
  have hs : count1337 q = (countLit q [-1, -2, -6]) + (countLit q [-10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1336)) (literal (valuationOf q) (1340)) (countLit q [-1, -2, -6]) (countLit q [-10, -12, -13]) (count1337 q) 1 3 (meaning1329 q) (meaning1336 q) (meaning1340 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1336 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1336 = false ∨ valuation q 1340 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1338 = true := by
  have hs : count1337 q = (countLit q [-1, -2, -6]) + (countLit q [-10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-10, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1330)) (literal (valuationOf q) (1338)) (countLit q [-1, -2, -6]) (countLit q [-10, -12, -13]) (count1337 q) 2 (meaning1330 q) (meaning1338 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1338 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1339 = true := by
  have hs : count1337 q = (countLit q [-1, -2, -6]) + (countLit q [-10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1334)) (literal (valuationOf q) (1339)) (countLit q [-1, -2, -6]) (countLit q [-10, -12, -13]) (count1337 q) 2 1 (meaning1330 q) (meaning1334 q) (meaning1339 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1334 = false ∨ valuation q 1339 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1335 = false ∨ valuationOf q 1340 = true := by
  have hs : count1337 q = (countLit q [-1, -2, -6]) + (countLit q [-10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1335)) (literal (valuationOf q) (1340)) (countLit q [-1, -2, -6]) (countLit q [-10, -12, -13]) (count1337 q) 2 2 (meaning1330 q) (meaning1335 q) (meaning1340 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1335 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1335 = false ∨ valuation q 1340 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1336 = false ∨ valuationOf q 1341 = true := by
  have hs : count1337 q = (countLit q [-1, -2, -6]) + (countLit q [-10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1336)) (literal (valuationOf q) (1341)) (countLit q [-1, -2, -6]) (countLit q [-10, -12, -13]) (count1337 q) 2 3 (meaning1330 q) (meaning1336 q) (meaning1341 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1336 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1336 = false ∨ valuation q 1341 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1339 = true := by
  have hs : count1337 q = (countLit q [-1, -2, -6]) + (countLit q [-10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-10, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1331)) (literal (valuationOf q) (1339)) (countLit q [-1, -2, -6]) (countLit q [-10, -12, -13]) (count1337 q) 3 (meaning1331 q) (meaning1339 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1339 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1340 = true := by
  have hs : count1337 q = (countLit q [-1, -2, -6]) + (countLit q [-10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1334)) (literal (valuationOf q) (1340)) (countLit q [-1, -2, -6]) (countLit q [-10, -12, -13]) (count1337 q) 3 1 (meaning1331 q) (meaning1334 q) (meaning1340 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1334 = false ∨ valuation q 1340 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1335 = false ∨ valuationOf q 1341 = true := by
  have hs : count1337 q = (countLit q [-1, -2, -6]) + (countLit q [-10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1335)) (literal (valuationOf q) (1341)) (countLit q [-1, -2, -6]) (countLit q [-10, -12, -13]) (count1337 q) 3 2 (meaning1331 q) (meaning1335 q) (meaning1341 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1335 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1335 = false ∨ valuation q 1341 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1343)) (countLit q [-16]) (countLit q [-18]) (count1343 q) 1 (meaningNeg18 q) (meaning1343 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1343 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1343)) (countLit q [-16]) (countLit q [-18]) (count1343 q) 1 (meaningNeg16 q) (meaning1343 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1343 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 18 = true ∨ valuationOf q 1344 = true := by
  have hs : count1343 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (1344)) (countLit q [-16]) (countLit q [-18]) (count1343 q) 1 1 (meaningNeg16 q) (meaningNeg18 q) (meaning1344 q) hs
  change (! (valuationOf q 16)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 18 = true ∨ valuation q 1344 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1345 = true := by
  have hs : count1345 q = (countLit q [-15]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16, -18])
  have hm := merge_right (literal (valuationOf q) (1343)) (literal (valuationOf q) (1345)) (countLit q [-15]) (countLit q [-16, -18]) (count1345 q) 1 (meaning1343 q) (meaning1345 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1345 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E148.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112148
