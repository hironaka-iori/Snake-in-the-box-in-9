import E112225Semantics
import B112E225Inputs
namespace Snake9.Regrowth.E112225
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_two (literal (valuationOf q) (307)) (literal (valuationOf q) (409)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 1 1 (meaning307 q) (meaning409 q) (meaning412 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 409 = false ∨ valuation q 412 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 308 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (308)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 2 (meaning308 q) (meaning412 q) hs
  change valuationOf q 308 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 308 = false ∨ valuation q 412 = true := counterClause322 (baseVal q)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 412 = false := by
  rw [value412]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count411 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause324 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1241 = true := by
  have hs : count1241 q = (countLit q [-4]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1241)) (countLit q [-4]) (countLit q [-7]) (count1241 q) 1 (meaningNeg7 q) (meaning1241 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1241 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1241 = true := by
  have hs : count1241 q = (countLit q [-4]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1241)) (countLit q [-4]) (countLit q [-7]) (count1241 q) 1 (meaningNeg4 q) (meaning1241 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1241 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 1241 = false ∨ valuationOf q 1243 = true := by
  have hs : count1243 q = (countLit q [-2]) + (countLit q [-4, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -7])
  have hm := merge_right (literal (valuationOf q) (1241)) (literal (valuationOf q) (1243)) (countLit q [-2]) (countLit q [-4, -7]) (count1243 q) 1 (meaning1241 q) (meaning1243 q) hs
  change valuationOf q 1241 = false ∨ valuationOf q 1243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 1241 = false ∨ valuation q 1243 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1243 = true := by
  have hs : count1243 q = (countLit q [-2]) + (countLit q [-4, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -7])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1243)) (countLit q [-2]) (countLit q [-4, -7]) (count1243 q) 1 (meaningNeg2 q) (meaning1243 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1243 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1243 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1246 = true := by
  have hs : count1246 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1246)) (countLit q [-11]) (countLit q [-13]) (count1246 q) 1 (meaningNeg13 q) (meaning1246 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1246 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1246 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1246 = true := by
  have hs : count1246 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1246)) (countLit q [-11]) (countLit q [-13]) (count1246 q) 1 (meaningNeg11 q) (meaning1246 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1246 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1246 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 1246 = false ∨ valuationOf q 1248 = true := by
  have hs : count1248 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_right (literal (valuationOf q) (1246)) (literal (valuationOf q) (1248)) (countLit q [-8]) (countLit q [-11, -13]) (count1248 q) 1 (meaning1246 q) (meaning1248 q) hs
  change valuationOf q 1246 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 1246 = false ∨ valuation q 1248 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1248 = true := by
  have hs : count1248 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1248)) (countLit q [-8]) (countLit q [-11, -13]) (count1248 q) 1 (meaningNeg8 q) (meaning1248 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1248 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 1248 = false ∨ valuationOf q 1251 = true := by
  have hs : count1251 q = (countLit q [-2, -4, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_right (literal (valuationOf q) (1248)) (literal (valuationOf q) (1251)) (countLit q [-2, -4, -7]) (countLit q [-8, -11, -13]) (count1251 q) 1 (meaning1248 q) (meaning1251 q) hs
  change valuationOf q 1248 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 1248 = false ∨ valuation q 1251 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1251 = true := by
  have hs : count1251 q = (countLit q [-2, -4, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_left (literal (valuationOf q) (1243)) (literal (valuationOf q) (1251)) (countLit q [-2, -4, -7]) (countLit q [-8, -11, -13]) (count1251 q) 1 (meaning1243 q) (meaning1251 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1251 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-17]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1257)) (countLit q [-17]) (countLit q [-18]) (count1257 q) 1 (meaningNeg18 q) (meaning1257 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1257 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-17]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1257)) (countLit q [-17]) (countLit q [-18]) (count1257 q) 1 (meaningNeg17 q) (meaning1257 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1257 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 1257 = false ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_right (literal (valuationOf q) (1257)) (literal (valuationOf q) (1259)) (countLit q [-15]) (countLit q [-17, -18]) (count1259 q) 1 (meaning1257 q) (meaning1259 q) hs
  change valuationOf q 1257 = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 1257 = false ∨ valuation q 1259 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1259)) (countLit q [-15]) (countLit q [-17, -18]) (count1259 q) 1 (meaningNeg15 q) (meaning1259 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1259 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1262 = true := by
  have hs : count1262 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1262)) (countLit q [-23]) (countLit q [-24]) (count1262 q) 1 (meaningNeg24 q) (meaning1262 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1262 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1264 = true := by
  have hs : count1264 q = (countLit q [-20]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-23, -24])
  have hm := merge_right (literal (valuationOf q) (1262)) (literal (valuationOf q) (1264)) (countLit q [-20]) (countLit q [-23, -24]) (count1264 q) 1 (meaning1262 q) (meaning1264 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1264 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1264 = true := by
  have hs : count1264 q = (countLit q [-20]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-23, -24])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1264)) (countLit q [-20]) (countLit q [-23, -24]) (count1264 q) 1 (meaningNeg20 q) (meaning1264 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1264 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1267 = true := by
  have hs : count1267 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1264)) (literal (valuationOf q) (1267)) (countLit q [-15, -17, -18]) (countLit q [-20, -23, -24]) (count1267 q) 1 (meaning1264 q) (meaning1267 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1267 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 1259 = false ∨ valuationOf q 1267 = true := by
  have hs : count1267 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1259)) (literal (valuationOf q) (1267)) (countLit q [-15, -17, -18]) (countLit q [-20, -23, -24]) (count1267 q) 1 (meaning1259 q) (meaning1267 q) hs
  change valuationOf q 1259 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 1259 = false ∨ valuation q 1267 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 1259 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1268 = true := by
  have hs : count1267 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1259)) (literal (valuationOf q) (1264)) (literal (valuationOf q) (1268)) (countLit q [-15, -17, -18]) (countLit q [-20, -23, -24]) (count1267 q) 1 1 (meaning1259 q) (meaning1264 q) (meaning1268 q) hs
  change valuationOf q 1259 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 1259 = false ∨ valuation q 1264 = false ∨ valuation q 1268 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 1267 = false ∨ valuationOf q 1273 = true := by
  have hs : count1273 q = (countLit q [-2, -4, -7, -8, -11, -13]) + (countLit q [-15, -17, -18, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13]) (l₂ := [-15, -17, -18, -20, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1267)) (literal (valuationOf q) (1273)) (countLit q [-2, -4, -7, -8, -11, -13]) (countLit q [-15, -17, -18, -20, -23, -24]) (count1273 q) 1 (meaning1267 q) (meaning1273 q) hs
  change valuationOf q 1267 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 1267 = false ∨ valuation q 1273 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 1268 = false ∨ valuationOf q 1274 = true := by
  have hs : count1273 q = (countLit q [-2, -4, -7, -8, -11, -13]) + (countLit q [-15, -17, -18, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13]) (l₂ := [-15, -17, -18, -20, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1268)) (literal (valuationOf q) (1274)) (countLit q [-2, -4, -7, -8, -11, -13]) (countLit q [-15, -17, -18, -20, -23, -24]) (count1273 q) 2 (meaning1268 q) (meaning1274 q) hs
  change valuationOf q 1268 = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 1268 = false ∨ valuation q 1274 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1274 = true := by
  have hs : count1273 q = (countLit q [-2, -4, -7, -8, -11, -13]) + (countLit q [-15, -17, -18, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13]) (l₂ := [-15, -17, -18, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1274)) (countLit q [-2, -4, -7, -8, -11, -13]) (countLit q [-15, -17, -18, -20, -23, -24]) (count1273 q) 1 1 (meaning1251 q) (meaning1267 q) (meaning1274 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1267 = false ∨ valuation q 1274 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1283 = true := by
  have hs : count1283 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1283)) (countLit q [-29]) (countLit q [-31]) (count1283 q) 1 (meaningNeg31 q) (meaning1283 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1283 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1283 = true := by
  have hs : count1283 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1283)) (countLit q [-29]) (countLit q [-31]) (count1283 q) 1 (meaningNeg29 q) (meaning1283 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1283 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1283 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 1283 = false ∨ valuationOf q 1285 = true := by
  have hs : count1285 q = (countLit q [-27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (1283)) (literal (valuationOf q) (1285)) (countLit q [-27]) (countLit q [-29, -31]) (count1285 q) 1 (meaning1283 q) (meaning1285 q) hs
  change valuationOf q 1283 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 1283 = false ∨ valuation q 1285 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1285 = true := by
  have hs : count1285 q = (countLit q [-27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -31])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1285)) (countLit q [-27]) (countLit q [-29, -31]) (count1285 q) 1 (meaningNeg27 q) (meaning1285 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1285 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1283 = false ∨ valuationOf q 1286 = true := by
  have hs : count1285 q = (countLit q [-27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (1283)) (literal (valuationOf q) (1286)) (countLit q [-27]) (countLit q [-29, -31]) (count1285 q) 1 1 (meaningNeg27 q) (meaning1283 q) (meaning1286 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1283 = false ∨ valuation q 1286 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (1288)) (countLit q [-34]) (countLit q [-36]) (count1288 q) 1 (meaningNeg36 q) (meaning1288 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1288 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E225.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112225
