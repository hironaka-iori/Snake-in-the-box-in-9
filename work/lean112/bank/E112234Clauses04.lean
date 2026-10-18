import E112234Semantics
import B112E234Inputs
namespace Snake9.Regrowth.E112234
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause129 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [122, 123, 124]) + (countLit q [125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124]) (l₂ := [125, 126, 127, 128])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (247)) (countLit q [122, 123, 124]) (countLit q [125, 126, 127, 128]) (count247 q) 1 (meaning239 q) (meaning247 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 247 = true := counterClause129 (baseVal q)

theorem counterClause130 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 247 = false ∨ valuationOf q 250 = true := by
  have hs : count249 q = (countLit q [116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128])
  have hm := merge_two (literal (valuationOf q) (235)) (literal (valuationOf q) (247)) (literal (valuationOf q) (250)) (countLit q [116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128]) (count249 q) 1 1 (meaning235 q) (meaning247 q) (meaning250 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 247 = false ∨ valuationOf q 250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 247 = false ∨ valuation q 250 = true := counterClause130 (baseVal q)

theorem counterClause131 (q : Nat → Bool) : valuationOf q 236 = false ∨ valuationOf q 250 = true := by
  have hs : count249 q = (countLit q [116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128])
  have hm := merge_left (literal (valuationOf q) (236)) (literal (valuationOf q) (250)) (countLit q [116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128]) (count249 q) 2 (meaning236 q) (meaning250 q) hs
  change valuationOf q 236 = false ∨ valuationOf q 250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 250 = true := counterClause131 (baseVal q)

theorem counterClause132 (q : Nat → Bool) : valuationOf q 250 = false ∨ valuationOf q 252 = true := by
  have hs : count251 q = (countLit q [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115]) + (countLit q [116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) := List.countP_append (p := literal q) (l₁ := [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115]) (l₂ := [116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128])
  have hm := merge_right (literal (valuationOf q) (250)) (literal (valuationOf q) (252)) (countLit q [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115]) (countLit q [116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (count251 q) 2 (meaning250 q) (meaning252 q) hs
  change valuationOf q 250 = false ∨ valuationOf q 252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 250 = false ∨ valuation q 252 = true := counterClause132 (baseVal q)

theorem counterClause133 (q : Nat → Bool) : valuationOf q 252 = false ∨ valuationOf q 302 = true := by
  have hs : count301 q = (countLit q [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) + (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153]) := List.countP_append (p := literal q) (l₁ := [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (l₂ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153])
  have hm := merge_left (literal (valuationOf q) (252)) (literal (valuationOf q) (302)) (countLit q [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153]) (count301 q) 2 (meaning252 q) (meaning302 q) hs
  change valuationOf q 252 = false ∨ valuationOf q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 252 = false ∨ valuation q 302 = true := counterClause133 (baseVal q)

theorem counterClause134 (q : Nat → Bool) : valuationOf q 302 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153]) + (countLit q [154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153]) (l₂ := [154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (302)) (literal (valuationOf q) (404)) (countLit q [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153]) (countLit q [154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (count403 q) 2 (meaning302 q) (meaning404 q) hs
  change valuationOf q 302 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 302 = false ∨ valuation q 404 = true := counterClause134 (baseVal q)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 404 = false := by
  rw [value404]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count403 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause136 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1190 = true := by
  have hs : count1190 q = (countLit q [-2]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1190)) (countLit q [-2]) (countLit q [-5]) (count1190 q) 1 (meaningNeg2 q) (meaning1190 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1190 = true := counterClause136 (baseVal q)

theorem counterClause137 (q : Nat → Bool) : valuationOf q 1190 = false ∨ valuationOf q 1192 = true := by
  have hs : count1192 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_right (literal (valuationOf q) (1190)) (literal (valuationOf q) (1192)) (countLit q [-1]) (countLit q [-2, -5]) (count1192 q) 1 (meaning1190 q) (meaning1192 q) hs
  change valuationOf q 1190 = false ∨ valuationOf q 1192 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 1190 = false ∨ valuation q 1192 = true := counterClause137 (baseVal q)

theorem counterClause138 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1195 = true := by
  have hs : count1195 q = (countLit q [-10]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1195)) (countLit q [-10]) (countLit q [-13]) (count1195 q) 1 (meaningNeg13 q) (meaning1195 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1195 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1195 = true := counterClause138 (baseVal q)

theorem counterClause139 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1195 = true := by
  have hs : count1195 q = (countLit q [-10]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1195)) (countLit q [-10]) (countLit q [-13]) (count1195 q) 1 (meaningNeg10 q) (meaning1195 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1195 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1195 = true := counterClause139 (baseVal q)

theorem counterClause140 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1196 = true := by
  have hs : count1195 q = (countLit q [-10]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1196)) (countLit q [-10]) (countLit q [-13]) (count1195 q) 1 1 (meaningNeg10 q) (meaningNeg13 q) (meaning1196 q) hs
  change (! (valuationOf q 10)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1196 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 13 = true ∨ valuation q 1196 = true := counterClause140 (baseVal q)

theorem counterClause141 (q : Nat → Bool) : valuationOf q 1195 = false ∨ valuationOf q 1197 = true := by
  have hs : count1197 q = (countLit q [-9]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10, -13])
  have hm := merge_right (literal (valuationOf q) (1195)) (literal (valuationOf q) (1197)) (countLit q [-9]) (countLit q [-10, -13]) (count1197 q) 1 (meaning1195 q) (meaning1197 q) hs
  change valuationOf q 1195 = false ∨ valuationOf q 1197 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 1195 = false ∨ valuation q 1197 = true := counterClause141 (baseVal q)

theorem counterClause142 (q : Nat → Bool) : valuationOf q 1196 = false ∨ valuationOf q 1198 = true := by
  have hs : count1197 q = (countLit q [-9]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10, -13])
  have hm := merge_right (literal (valuationOf q) (1196)) (literal (valuationOf q) (1198)) (countLit q [-9]) (countLit q [-10, -13]) (count1197 q) 2 (meaning1196 q) (meaning1198 q) hs
  change valuationOf q 1196 = false ∨ valuationOf q 1198 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 1196 = false ∨ valuation q 1198 = true := counterClause142 (baseVal q)

theorem counterClause143 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1197 = true := by
  have hs : count1197 q = (countLit q [-9]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10, -13])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (1197)) (countLit q [-9]) (countLit q [-10, -13]) (count1197 q) 1 (meaningNeg9 q) (meaning1197 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1197 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1197 = true := counterClause143 (baseVal q)

theorem counterClause144 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1195 = false ∨ valuationOf q 1198 = true := by
  have hs : count1197 q = (countLit q [-9]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10, -13])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (1195)) (literal (valuationOf q) (1198)) (countLit q [-9]) (countLit q [-10, -13]) (count1197 q) 1 1 (meaningNeg9 q) (meaning1195 q) (meaning1198 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1195 = false ∨ valuationOf q 1198 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1195 = false ∨ valuation q 1198 = true := counterClause144 (baseVal q)

theorem counterClause145 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1196 = false ∨ valuationOf q 1199 = true := by
  have hs : count1197 q = (countLit q [-9]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10, -13])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (1196)) (literal (valuationOf q) (1199)) (countLit q [-9]) (countLit q [-10, -13]) (count1197 q) 1 2 (meaningNeg9 q) (meaning1196 q) (meaning1199 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1196 = false ∨ valuationOf q 1199 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1196 = false ∨ valuation q 1199 = true := counterClause145 (baseVal q)

theorem counterClause146 (q : Nat → Bool) : valuationOf q 1197 = false ∨ valuationOf q 1200 = true := by
  have hs : count1200 q = (countLit q [-1, -2, -5]) + (countLit q [-9, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-9, -10, -13])
  have hm := merge_right (literal (valuationOf q) (1197)) (literal (valuationOf q) (1200)) (countLit q [-1, -2, -5]) (countLit q [-9, -10, -13]) (count1200 q) 1 (meaning1197 q) (meaning1200 q) hs
  change valuationOf q 1197 = false ∨ valuationOf q 1200 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 1197 = false ∨ valuation q 1200 = true := counterClause146 (baseVal q)

theorem counterClause147 (q : Nat → Bool) : valuationOf q 1198 = false ∨ valuationOf q 1201 = true := by
  have hs : count1200 q = (countLit q [-1, -2, -5]) + (countLit q [-9, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-9, -10, -13])
  have hm := merge_right (literal (valuationOf q) (1198)) (literal (valuationOf q) (1201)) (countLit q [-1, -2, -5]) (countLit q [-9, -10, -13]) (count1200 q) 2 (meaning1198 q) (meaning1201 q) hs
  change valuationOf q 1198 = false ∨ valuationOf q 1201 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 1198 = false ∨ valuation q 1201 = true := counterClause147 (baseVal q)

theorem counterClause148 (q : Nat → Bool) : valuationOf q 1199 = false ∨ valuationOf q 1202 = true := by
  have hs : count1200 q = (countLit q [-1, -2, -5]) + (countLit q [-9, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-9, -10, -13])
  have hm := merge_right (literal (valuationOf q) (1199)) (literal (valuationOf q) (1202)) (countLit q [-1, -2, -5]) (countLit q [-9, -10, -13]) (count1200 q) 3 (meaning1199 q) (meaning1202 q) hs
  change valuationOf q 1199 = false ∨ valuationOf q 1202 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 1199 = false ∨ valuation q 1202 = true := counterClause148 (baseVal q)

theorem counterClause149 (q : Nat → Bool) : valuationOf q 1192 = false ∨ valuationOf q 1200 = true := by
  have hs : count1200 q = (countLit q [-1, -2, -5]) + (countLit q [-9, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-9, -10, -13])
  have hm := merge_left (literal (valuationOf q) (1192)) (literal (valuationOf q) (1200)) (countLit q [-1, -2, -5]) (countLit q [-9, -10, -13]) (count1200 q) 1 (meaning1192 q) (meaning1200 q) hs
  change valuationOf q 1192 = false ∨ valuationOf q 1200 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 1192 = false ∨ valuation q 1200 = true := counterClause149 (baseVal q)

theorem counterClause150 (q : Nat → Bool) : valuationOf q 1192 = false ∨ valuationOf q 1197 = false ∨ valuationOf q 1201 = true := by
  have hs : count1200 q = (countLit q [-1, -2, -5]) + (countLit q [-9, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-9, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1192)) (literal (valuationOf q) (1197)) (literal (valuationOf q) (1201)) (countLit q [-1, -2, -5]) (countLit q [-9, -10, -13]) (count1200 q) 1 1 (meaning1192 q) (meaning1197 q) (meaning1201 q) hs
  change valuationOf q 1192 = false ∨ valuationOf q 1197 = false ∨ valuationOf q 1201 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 1192 = false ∨ valuation q 1197 = false ∨ valuation q 1201 = true := counterClause150 (baseVal q)

theorem counterClause151 (q : Nat → Bool) : valuationOf q 1192 = false ∨ valuationOf q 1198 = false ∨ valuationOf q 1202 = true := by
  have hs : count1200 q = (countLit q [-1, -2, -5]) + (countLit q [-9, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-9, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1192)) (literal (valuationOf q) (1198)) (literal (valuationOf q) (1202)) (countLit q [-1, -2, -5]) (countLit q [-9, -10, -13]) (count1200 q) 1 2 (meaning1192 q) (meaning1198 q) (meaning1202 q) hs
  change valuationOf q 1192 = false ∨ valuationOf q 1198 = false ∨ valuationOf q 1202 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 1192 = false ∨ valuation q 1198 = false ∨ valuation q 1202 = true := counterClause151 (baseVal q)

theorem counterClause152 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1206 = true := by
  have hs : count1206 q = (countLit q [-16]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1206)) (countLit q [-16]) (countLit q [-19]) (count1206 q) 1 (meaningNeg19 q) (meaning1206 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1206 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1206 = true := counterClause152 (baseVal q)

theorem counterClause153 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1206 = true := by
  have hs : count1206 q = (countLit q [-16]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1206)) (countLit q [-16]) (countLit q [-19]) (count1206 q) 1 (meaningNeg16 q) (meaning1206 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1206 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1206 = true := counterClause153 (baseVal q)

theorem counterClause154 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 19 = true ∨ valuationOf q 1207 = true := by
  have hs : count1206 q = (countLit q [-16]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (1207)) (countLit q [-16]) (countLit q [-19]) (count1206 q) 1 1 (meaningNeg16 q) (meaningNeg19 q) (meaning1207 q) hs
  change (! (valuationOf q 16)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 1207 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 19 = true ∨ valuation q 1207 = true := counterClause154 (baseVal q)

theorem counterClause155 (q : Nat → Bool) : valuationOf q 1206 = false ∨ valuationOf q 1208 = true := by
  have hs : count1208 q = (countLit q [-14]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -19])
  have hm := merge_right (literal (valuationOf q) (1206)) (literal (valuationOf q) (1208)) (countLit q [-14]) (countLit q [-16, -19]) (count1208 q) 1 (meaning1206 q) (meaning1208 q) hs
  change valuationOf q 1206 = false ∨ valuationOf q 1208 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 1206 = false ∨ valuation q 1208 = true := counterClause155 (baseVal q)

theorem counterClause156 (q : Nat → Bool) : valuationOf q 1207 = false ∨ valuationOf q 1209 = true := by
  have hs : count1208 q = (countLit q [-14]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -19])
  have hm := merge_right (literal (valuationOf q) (1207)) (literal (valuationOf q) (1209)) (countLit q [-14]) (countLit q [-16, -19]) (count1208 q) 2 (meaning1207 q) (meaning1209 q) hs
  change valuationOf q 1207 = false ∨ valuationOf q 1209 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 1207 = false ∨ valuation q 1209 = true := counterClause156 (baseVal q)

theorem counterClause157 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1208 = true := by
  have hs : count1208 q = (countLit q [-14]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -19])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1208)) (countLit q [-14]) (countLit q [-16, -19]) (count1208 q) 1 (meaningNeg14 q) (meaning1208 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1208 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1208 = true := counterClause157 (baseVal q)

theorem counterClause158 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1206 = false ∨ valuationOf q 1209 = true := by
  have hs : count1208 q = (countLit q [-14]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -19])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (1206)) (literal (valuationOf q) (1209)) (countLit q [-14]) (countLit q [-16, -19]) (count1208 q) 1 1 (meaningNeg14 q) (meaning1206 q) (meaning1209 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1206 = false ∨ valuationOf q 1209 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1206 = false ∨ valuation q 1209 = true := counterClause158 (baseVal q)

theorem counterClause159 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1207 = false ∨ valuationOf q 1210 = true := by
  have hs : count1208 q = (countLit q [-14]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -19])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (1207)) (literal (valuationOf q) (1210)) (countLit q [-14]) (countLit q [-16, -19]) (count1208 q) 1 2 (meaningNeg14 q) (meaning1207 q) (meaning1210 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1207 = false ∨ valuationOf q 1210 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1207 = false ∨ valuation q 1210 = true := counterClause159 (baseVal q)

theorem counterClause160 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1211 = true := by
  have hs : count1211 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (1211)) (countLit q [-22]) (countLit q [-25]) (count1211 q) 1 (meaningNeg25 q) (meaning1211 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1211 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1211 = true := counterClause160 (baseVal q)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E234.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112234
