import E112150Semantics
import B112E150Inputs
namespace Snake9.Regrowth.E112150
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause161 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185])
  have hm := merge_right (literal (valuationOf q) (361)) (literal (valuationOf q) (363)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185]) (count363 q) 1 (meaning361 q) (meaning363 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 363 = true := counterClause161 (baseVal q)

theorem counterClause162 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185])
  have hm := merge_left (literal (valuationOf q) (337)) (literal (valuationOf q) (363)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185]) (count363 q) 1 (meaning337 q) (meaning363 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 363 = true := counterClause162 (baseVal q)

theorem counterClause163 (q : Nat → Bool) : valuationOf q 210 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_right (literal (valuationOf q) (210)) (literal (valuationOf q) (405)) (countLit q [209]) (countLit q [210]) (count405 q) 1 (meaning210 q) (meaning405 q) hs
  change valuationOf q 210 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 405 = true := counterClause163 (baseVal q)

theorem counterClause164 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [209, 210]) + (countLit q [211, 212]) := List.countP_append (p := literal q) (l₁ := [209, 210]) (l₂ := [211, 212])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (409)) (countLit q [209, 210]) (countLit q [211, 212]) (count409 q) 1 (meaning405 q) (meaning409 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 409 = true := counterClause164 (baseVal q)

theorem counterClause165 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [206, 207, 208]) + (countLit q [209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208]) (l₂ := [209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [206, 207, 208]) (countLit q [209, 210, 211, 212]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause165 (baseVal q)

theorem counterClause166 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (411)) (literal (valuationOf q) (413)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212]) (count413 q) 1 (meaning411 q) (meaning413 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 413 = true := counterClause166 (baseVal q)

theorem counterClause167 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause167 (baseVal q)

theorem counterClause168 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (363)) (literal (valuationOf q) (415)) (literal (valuationOf q) (418)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 1 (meaning363 q) (meaning415 q) (meaning418 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 415 = false ∨ valuation q 418 = true := counterClause168 (baseVal q)

theorem counterClause169 (q : Nat → Bool) : valuationOf q 418 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (418)) (literal (valuationOf q) (420)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count419 q) 2 (meaning418 q) (meaning420 q) hs
  change valuationOf q 418 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 420 = true := counterClause169 (baseVal q)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 420 = false := by
  rw [value420]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count419 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause171 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1261 = true := by
  have hs : count1261 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1261)) (countLit q [-3]) (countLit q [-5]) (count1261 q) 1 (meaningNeg5 q) (meaning1261 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1261 = true := counterClause171 (baseVal q)

theorem counterClause172 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1261 = true := by
  have hs : count1261 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1261)) (countLit q [-3]) (countLit q [-5]) (count1261 q) 1 (meaningNeg3 q) (meaning1261 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1261 = true := counterClause172 (baseVal q)

theorem counterClause173 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1262 = true := by
  have hs : count1261 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1262)) (countLit q [-3]) (countLit q [-5]) (count1261 q) 1 1 (meaningNeg3 q) (meaningNeg5 q) (meaning1262 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 5 = true ∨ valuation q 1262 = true := counterClause173 (baseVal q)

theorem counterClause174 (q : Nat → Bool) : valuationOf q 1261 = false ∨ valuationOf q 1263 = true := by
  have hs : count1263 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1261)) (literal (valuationOf q) (1263)) (countLit q [-2]) (countLit q [-3, -5]) (count1263 q) 1 (meaning1261 q) (meaning1263 q) hs
  change valuationOf q 1261 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 1261 = false ∨ valuation q 1263 = true := counterClause174 (baseVal q)

theorem counterClause175 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1264 = true := by
  have hs : count1263 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1262)) (literal (valuationOf q) (1264)) (countLit q [-2]) (countLit q [-3, -5]) (count1263 q) 2 (meaning1262 q) (meaning1264 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1264 = true := counterClause175 (baseVal q)

theorem counterClause176 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1263 = true := by
  have hs : count1263 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1263)) (countLit q [-2]) (countLit q [-3, -5]) (count1263 q) 1 (meaningNeg2 q) (meaning1263 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1263 = true := counterClause176 (baseVal q)

theorem counterClause177 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1261 = false ∨ valuationOf q 1264 = true := by
  have hs : count1263 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1261)) (literal (valuationOf q) (1264)) (countLit q [-2]) (countLit q [-3, -5]) (count1263 q) 1 1 (meaningNeg2 q) (meaning1261 q) (meaning1264 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1261 = false ∨ valuation q 1264 = true := counterClause177 (baseVal q)

theorem counterClause178 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1266 = true := by
  have hs : count1266 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1266)) (countLit q [-11]) (countLit q [-12]) (count1266 q) 1 (meaningNeg12 q) (meaning1266 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1266 = true := counterClause178 (baseVal q)

theorem counterClause179 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1266 = true := by
  have hs : count1266 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1266)) (countLit q [-11]) (countLit q [-12]) (count1266 q) 1 (meaningNeg11 q) (meaning1266 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1266 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 12 = true ∨ valuationOf q 1267 = true := by
  have hs : count1266 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (1267)) (countLit q [-11]) (countLit q [-12]) (count1266 q) 1 1 (meaningNeg11 q) (meaningNeg12 q) (meaning1267 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 12 = true ∨ valuation q 1267 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 1266 = false ∨ valuationOf q 1268 = true := by
  have hs : count1268 q = (countLit q [-7]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (1266)) (literal (valuationOf q) (1268)) (countLit q [-7]) (countLit q [-11, -12]) (count1268 q) 1 (meaning1266 q) (meaning1268 q) hs
  change valuationOf q 1266 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 1266 = false ∨ valuation q 1268 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 1267 = false ∨ valuationOf q 1269 = true := by
  have hs : count1268 q = (countLit q [-7]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (1267)) (literal (valuationOf q) (1269)) (countLit q [-7]) (countLit q [-11, -12]) (count1268 q) 2 (meaning1267 q) (meaning1269 q) hs
  change valuationOf q 1267 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 1267 = false ∨ valuation q 1269 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1268 = true := by
  have hs : count1268 q = (countLit q [-7]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-11, -12])
  have hm := merge_left (literal (valuationOf q) (-7)) (literal (valuationOf q) (1268)) (countLit q [-7]) (countLit q [-11, -12]) (count1268 q) 1 (meaningNeg7 q) (meaning1268 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1268 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1266 = false ∨ valuationOf q 1269 = true := by
  have hs : count1268 q = (countLit q [-7]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (-7)) (literal (valuationOf q) (1266)) (literal (valuationOf q) (1269)) (countLit q [-7]) (countLit q [-11, -12]) (count1268 q) 1 1 (meaningNeg7 q) (meaning1266 q) (meaning1269 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1266 = false ∨ valuation q 1269 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1267 = false ∨ valuationOf q 1270 = true := by
  have hs : count1268 q = (countLit q [-7]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (-7)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1270)) (countLit q [-7]) (countLit q [-11, -12]) (count1268 q) 1 2 (meaningNeg7 q) (meaning1267 q) (meaning1270 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1267 = false ∨ valuation q 1270 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1272 = true := by
  have hs : count1271 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -11, -12])
  have hm := merge_right (literal (valuationOf q) (1269)) (literal (valuationOf q) (1272)) (countLit q [-2, -3, -5]) (countLit q [-7, -11, -12]) (count1271 q) 2 (meaning1269 q) (meaning1272 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1272 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1273 = true := by
  have hs : count1271 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -11, -12])
  have hm := merge_right (literal (valuationOf q) (1270)) (literal (valuationOf q) (1273)) (countLit q [-2, -3, -5]) (countLit q [-7, -11, -12]) (count1271 q) 3 (meaning1270 q) (meaning1273 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1273 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1271 = true := by
  have hs : count1271 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -11, -12])
  have hm := merge_left (literal (valuationOf q) (1263)) (literal (valuationOf q) (1271)) (countLit q [-2, -3, -5]) (countLit q [-7, -11, -12]) (count1271 q) 1 (meaning1263 q) (meaning1271 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1271 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1272 = true := by
  have hs : count1271 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1268)) (literal (valuationOf q) (1272)) (countLit q [-2, -3, -5]) (countLit q [-7, -11, -12]) (count1271 q) 1 1 (meaning1263 q) (meaning1268 q) (meaning1272 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1268 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1268 = false ∨ valuation q 1272 = true := counterClause189 (baseVal q)

theorem counterClause190 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1269 = false ∨ valuationOf q 1273 = true := by
  have hs : count1271 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1269)) (literal (valuationOf q) (1273)) (countLit q [-2, -3, -5]) (countLit q [-7, -11, -12]) (count1271 q) 1 2 (meaning1263 q) (meaning1269 q) (meaning1273 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1269 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1269 = false ∨ valuation q 1273 = true := counterClause190 (baseVal q)

theorem counterClause191 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1270 = false ∨ valuationOf q 1274 = true := by
  have hs : count1271 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1270)) (literal (valuationOf q) (1274)) (countLit q [-2, -3, -5]) (countLit q [-7, -11, -12]) (count1271 q) 1 3 (meaning1263 q) (meaning1270 q) (meaning1274 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1270 = false ∨ valuationOf q 1274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1270 = false ∨ valuation q 1274 = true := counterClause191 (baseVal q)

theorem counterClause192 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1272 = true := by
  have hs : count1271 q = (countLit q [-2, -3, -5]) + (countLit q [-7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-7, -11, -12])
  have hm := merge_left (literal (valuationOf q) (1264)) (literal (valuationOf q) (1272)) (countLit q [-2, -3, -5]) (countLit q [-7, -11, -12]) (count1271 q) 2 (meaning1264 q) (meaning1272 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1272 = true := counterClause192 (baseVal q)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E150.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112150
