import E112242Semantics
import B112E242Inputs
namespace Snake9.Regrowth.E112242
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause65 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [205]) + (countLit q [206]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206])
  have hm := merge_right (literal (valuationOf q) (206)) (literal (valuationOf q) (397)) (countLit q [205]) (countLit q [206]) (count397 q) 1 (meaning206 q) (meaning397 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 397 = true := counterClause65 (baseVal q)

theorem counterClause66 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [207]) + (countLit q [208]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208])
  have hm := merge_right (literal (valuationOf q) (208)) (literal (valuationOf q) (399)) (countLit q [207]) (countLit q [208]) (count399 q) 1 (meaning208 q) (meaning399 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 399 = true := counterClause66 (baseVal q)

theorem counterClause67 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = false ∨ valuationOf q 402 = true := by
  have hs : count401 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_two (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (literal (valuationOf q) (402)) (countLit q [205, 206]) (countLit q [207, 208]) (count401 q) 1 1 (meaning397 q) (meaning399 q) (meaning402 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = false ∨ valuationOf q 402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = false ∨ valuation q 402 = true := counterClause67 (baseVal q)

theorem counterClause68 (q : Nat → Bool) : valuationOf q 402 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (402)) (literal (valuationOf q) (404)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count403 q) 2 (meaning402 q) (meaning404 q) hs
  change valuationOf q 402 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 402 = false ∨ valuation q 404 = true := counterClause68 (baseVal q)

theorem counterClause69 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (404)) (literal (valuationOf q) (406)) (countLit q [196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count405 q) 2 (meaning404 q) (meaning406 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 406 = true := counterClause69 (baseVal q)

theorem counterClause70 (q : Nat → Bool) : valuationOf q 406 = false ∨ valuationOf q 408 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (406)) (literal (valuationOf q) (408)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 2 (meaning406 q) (meaning408 q) hs
  change valuationOf q 406 = false ∨ valuationOf q 408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 406 = false ∨ valuation q 408 = true := counterClause70 (baseVal q)

theorem counterClause71 (q : Nat → Bool) : valuationOf q 408 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (408)) (literal (valuationOf q) (410)) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 2 (meaning408 q) (meaning410 q) hs
  change valuationOf q 408 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 408 = false ∨ valuation q 410 = true := counterClause71 (baseVal q)

theorem counterClause72 (q : Nat → Bool) : valuationOf q 410 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (410)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 2 (meaning410 q) (meaning412 q) hs
  change valuationOf q 410 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 410 = false ∨ valuation q 412 = true := counterClause72 (baseVal q)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 412 = false := by
  rw [value412]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count411 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause74 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1190 = true := by
  have hs : count1190 q = (countLit q [-3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1190)) (countLit q [-3]) (countLit q [-4, -5]) (count1190 q) 1 (meaningNeg3 q) (meaning1190 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1190 = true := counterClause74 (baseVal q)

theorem counterClause75 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1193 = true := by
  have hs : count1193 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1193)) (countLit q [-10]) (countLit q [-12]) (count1193 q) 1 (meaningNeg12 q) (meaning1193 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1193 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1193 = true := counterClause75 (baseVal q)

theorem counterClause76 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1193 = true := by
  have hs : count1193 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1193)) (countLit q [-10]) (countLit q [-12]) (count1193 q) 1 (meaningNeg10 q) (meaning1193 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1193 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1193 = true := counterClause76 (baseVal q)

theorem counterClause77 (q : Nat → Bool) : valuationOf q 1193 = false ∨ valuationOf q 1195 = true := by
  have hs : count1195 q = (countLit q [-6]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-10, -12])
  have hm := merge_right (literal (valuationOf q) (1193)) (literal (valuationOf q) (1195)) (countLit q [-6]) (countLit q [-10, -12]) (count1195 q) 1 (meaning1193 q) (meaning1195 q) hs
  change valuationOf q 1193 = false ∨ valuationOf q 1195 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 1193 = false ∨ valuation q 1195 = true := counterClause77 (baseVal q)

theorem counterClause78 (q : Nat → Bool) : valuationOf q 1195 = false ∨ valuationOf q 1198 = true := by
  have hs : count1198 q = (countLit q [-3, -4, -5]) + (countLit q [-6, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-6, -10, -12])
  have hm := merge_right (literal (valuationOf q) (1195)) (literal (valuationOf q) (1198)) (countLit q [-3, -4, -5]) (countLit q [-6, -10, -12]) (count1198 q) 1 (meaning1195 q) (meaning1198 q) hs
  change valuationOf q 1195 = false ∨ valuationOf q 1198 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 1195 = false ∨ valuation q 1198 = true := counterClause78 (baseVal q)

theorem counterClause79 (q : Nat → Bool) : valuationOf q 1190 = false ∨ valuationOf q 1198 = true := by
  have hs : count1198 q = (countLit q [-3, -4, -5]) + (countLit q [-6, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-6, -10, -12])
  have hm := merge_left (literal (valuationOf q) (1190)) (literal (valuationOf q) (1198)) (countLit q [-3, -4, -5]) (countLit q [-6, -10, -12]) (count1198 q) 1 (meaning1190 q) (meaning1198 q) hs
  change valuationOf q 1190 = false ∨ valuationOf q 1198 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 1190 = false ∨ valuation q 1198 = true := counterClause79 (baseVal q)

theorem counterClause80 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1204 = true := by
  have hs : count1204 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1204)) (countLit q [-15]) (countLit q [-17]) (count1204 q) 1 (meaningNeg17 q) (meaning1204 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1204 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1204 = true := counterClause80 (baseVal q)

theorem counterClause81 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1204 = true := by
  have hs : count1204 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1204)) (countLit q [-15]) (countLit q [-17]) (count1204 q) 1 (meaningNeg15 q) (meaning1204 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1204 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1204 = true := counterClause81 (baseVal q)

theorem counterClause82 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 17 = true ∨ valuationOf q 1205 = true := by
  have hs : count1204 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (1205)) (countLit q [-15]) (countLit q [-17]) (count1204 q) 1 1 (meaningNeg15 q) (meaningNeg17 q) (meaning1205 q) hs
  change (! (valuationOf q 15)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 1205 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 1205 = true := counterClause82 (baseVal q)

theorem counterClause83 (q : Nat → Bool) : valuationOf q 1204 = false ∨ valuationOf q 1206 = true := by
  have hs : count1206 q = (countLit q [-13]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -17])
  have hm := merge_right (literal (valuationOf q) (1204)) (literal (valuationOf q) (1206)) (countLit q [-13]) (countLit q [-15, -17]) (count1206 q) 1 (meaning1204 q) (meaning1206 q) hs
  change valuationOf q 1204 = false ∨ valuationOf q 1206 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 1204 = false ∨ valuation q 1206 = true := counterClause83 (baseVal q)

theorem counterClause84 (q : Nat → Bool) : valuationOf q 1205 = false ∨ valuationOf q 1207 = true := by
  have hs : count1206 q = (countLit q [-13]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -17])
  have hm := merge_right (literal (valuationOf q) (1205)) (literal (valuationOf q) (1207)) (countLit q [-13]) (countLit q [-15, -17]) (count1206 q) 2 (meaning1205 q) (meaning1207 q) hs
  change valuationOf q 1205 = false ∨ valuationOf q 1207 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 1205 = false ∨ valuation q 1207 = true := counterClause84 (baseVal q)

theorem counterClause85 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1204 = false ∨ valuationOf q 1207 = true := by
  have hs : count1206 q = (countLit q [-13]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -17])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (1204)) (literal (valuationOf q) (1207)) (countLit q [-13]) (countLit q [-15, -17]) (count1206 q) 1 1 (meaningNeg13 q) (meaning1204 q) (meaning1207 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1204 = false ∨ valuationOf q 1207 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1204 = false ∨ valuation q 1207 = true := counterClause85 (baseVal q)

theorem counterClause86 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1209 = true := by
  have hs : count1209 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (1209)) (countLit q [-18]) (countLit q [-20]) (count1209 q) 1 (meaningNeg20 q) (meaning1209 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1209 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1209 = true := counterClause86 (baseVal q)

theorem counterClause87 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1209 = true := by
  have hs : count1209 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1209)) (countLit q [-18]) (countLit q [-20]) (count1209 q) 1 (meaningNeg18 q) (meaning1209 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1209 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1209 = true := counterClause87 (baseVal q)

theorem counterClause88 (q : Nat → Bool) : valuationOf q 1209 = false ∨ valuationOf q 1213 = true := by
  have hs : count1213 q = (countLit q [-18, -20]) + (countLit q [-22, -27]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-22, -27])
  have hm := merge_left (literal (valuationOf q) (1209)) (literal (valuationOf q) (1213)) (countLit q [-18, -20]) (countLit q [-22, -27]) (count1213 q) 1 (meaning1209 q) (meaning1213 q) hs
  change valuationOf q 1209 = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 1209 = false ∨ valuation q 1213 = true := counterClause88 (baseVal q)

theorem counterClause89 (q : Nat → Bool) : valuationOf q 1213 = false ∨ valuationOf q 1217 = true := by
  have hs : count1217 q = (countLit q [-13, -15, -17]) + (countLit q [-18, -20, -22, -27]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -17]) (l₂ := [-18, -20, -22, -27])
  have hm := merge_right (literal (valuationOf q) (1213)) (literal (valuationOf q) (1217)) (countLit q [-13, -15, -17]) (countLit q [-18, -20, -22, -27]) (count1217 q) 1 (meaning1213 q) (meaning1217 q) hs
  change valuationOf q 1213 = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 1213 = false ∨ valuation q 1217 = true := counterClause89 (baseVal q)

theorem counterClause90 (q : Nat → Bool) : valuationOf q 1206 = false ∨ valuationOf q 1217 = true := by
  have hs : count1217 q = (countLit q [-13, -15, -17]) + (countLit q [-18, -20, -22, -27]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -17]) (l₂ := [-18, -20, -22, -27])
  have hm := merge_left (literal (valuationOf q) (1206)) (literal (valuationOf q) (1217)) (countLit q [-13, -15, -17]) (countLit q [-18, -20, -22, -27]) (count1217 q) 1 (meaning1206 q) (meaning1217 q) hs
  change valuationOf q 1206 = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 1206 = false ∨ valuation q 1217 = true := counterClause90 (baseVal q)

theorem counterClause91 (q : Nat → Bool) : valuationOf q 1206 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1218 = true := by
  have hs : count1217 q = (countLit q [-13, -15, -17]) + (countLit q [-18, -20, -22, -27]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -17]) (l₂ := [-18, -20, -22, -27])
  have hm := merge_two (literal (valuationOf q) (1206)) (literal (valuationOf q) (1213)) (literal (valuationOf q) (1218)) (countLit q [-13, -15, -17]) (countLit q [-18, -20, -22, -27]) (count1217 q) 1 1 (meaning1206 q) (meaning1213 q) (meaning1218 q) hs
  change valuationOf q 1206 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 1206 = false ∨ valuation q 1213 = false ∨ valuation q 1218 = true := counterClause91 (baseVal q)

theorem counterClause92 (q : Nat → Bool) : valuationOf q 1207 = false ∨ valuationOf q 1218 = true := by
  have hs : count1217 q = (countLit q [-13, -15, -17]) + (countLit q [-18, -20, -22, -27]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -17]) (l₂ := [-18, -20, -22, -27])
  have hm := merge_left (literal (valuationOf q) (1207)) (literal (valuationOf q) (1218)) (countLit q [-13, -15, -17]) (countLit q [-18, -20, -22, -27]) (count1217 q) 2 (meaning1207 q) (meaning1218 q) hs
  change valuationOf q 1207 = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 1207 = false ∨ valuation q 1218 = true := counterClause92 (baseVal q)

theorem counterClause93 (q : Nat → Bool) : valuationOf q 1198 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1225 = true := by
  have hs : count1224 q = (countLit q [-3, -4, -5, -6, -10, -12]) + (countLit q [-13, -15, -17, -18, -20, -22, -27]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -6, -10, -12]) (l₂ := [-13, -15, -17, -18, -20, -22, -27])
  have hm := merge_two (literal (valuationOf q) (1198)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1225)) (countLit q [-3, -4, -5, -6, -10, -12]) (countLit q [-13, -15, -17, -18, -20, -22, -27]) (count1224 q) 1 1 (meaning1198 q) (meaning1217 q) (meaning1225 q) hs
  change valuationOf q 1198 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 1198 = false ∨ valuation q 1217 = false ∨ valuation q 1225 = true := counterClause93 (baseVal q)

theorem counterClause94 (q : Nat → Bool) : valuationOf q 1198 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1226 = true := by
  have hs : count1224 q = (countLit q [-3, -4, -5, -6, -10, -12]) + (countLit q [-13, -15, -17, -18, -20, -22, -27]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -6, -10, -12]) (l₂ := [-13, -15, -17, -18, -20, -22, -27])
  have hm := merge_two (literal (valuationOf q) (1198)) (literal (valuationOf q) (1218)) (literal (valuationOf q) (1226)) (countLit q [-3, -4, -5, -6, -10, -12]) (countLit q [-13, -15, -17, -18, -20, -22, -27]) (count1224 q) 1 2 (meaning1198 q) (meaning1218 q) (meaning1226 q) hs
  change valuationOf q 1198 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1226 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 1198 = false ∨ valuation q 1218 = false ∨ valuation q 1226 = true := counterClause94 (baseVal q)

theorem counterClause95 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1237 = true := by
  have hs : count1237 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1237)) (countLit q [-29]) (countLit q [-31]) (count1237 q) 1 (meaningNeg31 q) (meaning1237 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1237 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1237 = true := counterClause95 (baseVal q)

theorem counterClause96 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1237 = true := by
  have hs : count1237 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1237)) (countLit q [-29]) (countLit q [-31]) (count1237 q) 1 (meaningNeg29 q) (meaning1237 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1237 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1237 = true := counterClause96 (baseVal q)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E242.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112242
