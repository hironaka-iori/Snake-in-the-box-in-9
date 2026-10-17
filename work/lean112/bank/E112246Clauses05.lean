import E112246Semantics
import B112E246Inputs
namespace Snake9.Regrowth.E112246
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause161 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (399)) (countLit q [199, 200, 201]) (countLit q [202, 203, 204, 205]) (count399 q) 1 (meaning391 q) (meaning399 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 399 = true := counterClause161 (baseVal q)

theorem counterClause162 (q : Nat → Bool) : valuationOf q 210 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_right (literal (valuationOf q) (210)) (literal (valuationOf q) (405)) (countLit q [209]) (countLit q [210]) (count405 q) 1 (meaning210 q) (meaning405 q) hs
  change valuationOf q 210 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 405 = true := counterClause162 (baseVal q)

theorem counterClause163 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [211]) + (countLit q [212]) := List.countP_append (p := literal q) (l₁ := [211]) (l₂ := [212])
  have hm := merge_right (literal (valuationOf q) (212)) (literal (valuationOf q) (407)) (countLit q [211]) (countLit q [212]) (count407 q) 1 (meaning212 q) (meaning407 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 407 = true := counterClause163 (baseVal q)

theorem counterClause164 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [209, 210]) + (countLit q [211, 212]) := List.countP_append (p := literal q) (l₁ := [209, 210]) (l₂ := [211, 212])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [209, 210]) (countLit q [211, 212]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause164 (baseVal q)

theorem counterClause165 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [209, 210]) + (countLit q [211, 212]) := List.countP_append (p := literal q) (l₁ := [209, 210]) (l₂ := [211, 212])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (409)) (countLit q [209, 210]) (countLit q [211, 212]) (count409 q) 1 (meaning405 q) (meaning409 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 409 = true := counterClause165 (baseVal q)

theorem counterClause166 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [206, 207, 208]) + (countLit q [209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208]) (l₂ := [209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [206, 207, 208]) (countLit q [209, 210, 211, 212]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause166 (baseVal q)

theorem counterClause167 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (411)) (literal (valuationOf q) (413)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212]) (count413 q) 1 (meaning411 q) (meaning413 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 413 = true := counterClause167 (baseVal q)

theorem counterClause168 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (399)) (literal (valuationOf q) (413)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212]) (count413 q) 1 (meaning399 q) (meaning413 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 413 = true := counterClause168 (baseVal q)

theorem counterClause169 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 411 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (399)) (literal (valuationOf q) (411)) (literal (valuationOf q) (414)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212]) (count413 q) 1 1 (meaning399 q) (meaning411 q) (meaning414 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 411 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 411 = false ∨ valuation q 414 = true := counterClause169 (baseVal q)

theorem counterClause170 (q : Nat → Bool) : valuationOf q 414 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (414)) (literal (valuationOf q) (416)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 2 (meaning414 q) (meaning416 q) hs
  change valuationOf q 414 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 414 = false ∨ valuation q 416 = true := counterClause170 (baseVal q)

theorem counterClause171 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 413 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (387)) (literal (valuationOf q) (413)) (literal (valuationOf q) (416)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 1 (meaning387 q) (meaning413 q) (meaning416 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 413 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 413 = false ∨ valuation q 416 = true := counterClause171 (baseVal q)

theorem counterClause172 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (388)) (literal (valuationOf q) (416)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 2 (meaning388 q) (meaning416 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 416 = true := counterClause172 (baseVal q)

theorem counterClause173 (q : Nat → Bool) : valuationOf q 416 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (416)) (literal (valuationOf q) (418)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 2 (meaning416 q) (meaning418 q) hs
  change valuationOf q 416 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 416 = false ∨ valuation q 418 = true := counterClause173 (baseVal q)

theorem counterClause174 (q : Nat → Bool) : valuationOf q 418 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (418)) (literal (valuationOf q) (420)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count419 q) 2 (meaning418 q) (meaning420 q) hs
  change valuationOf q 418 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 420 = true := counterClause174 (baseVal q)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 420 = false := by
  rw [value420]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count419 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause176 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1252 = true := by
  have hs : count1252 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1252)) (countLit q [-4]) (countLit q [-5]) (count1252 q) 1 (meaningNeg4 q) (meaning1252 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1252 = true := counterClause176 (baseVal q)

theorem counterClause177 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1253 = true := by
  have hs : count1252 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1253)) (countLit q [-4]) (countLit q [-5]) (count1252 q) 1 1 (meaningNeg4 q) (meaningNeg5 q) (meaning1253 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 1253 = true := counterClause177 (baseVal q)

theorem counterClause178 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1254 = true := by
  have hs : count1254 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1252)) (literal (valuationOf q) (1254)) (countLit q [-2]) (countLit q [-4, -5]) (count1254 q) 1 (meaning1252 q) (meaning1254 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1254 = true := counterClause178 (baseVal q)

theorem counterClause179 (q : Nat → Bool) : valuationOf q 1253 = false ∨ valuationOf q 1255 = true := by
  have hs : count1254 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1253)) (literal (valuationOf q) (1255)) (countLit q [-2]) (countLit q [-4, -5]) (count1254 q) 2 (meaning1253 q) (meaning1255 q) hs
  change valuationOf q 1253 = false ∨ valuationOf q 1255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 1253 = false ∨ valuation q 1255 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1254 = true := by
  have hs : count1254 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1254)) (countLit q [-2]) (countLit q [-4, -5]) (count1254 q) 1 (meaningNeg2 q) (meaning1254 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1254 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1252 = false ∨ valuationOf q 1255 = true := by
  have hs : count1254 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1252)) (literal (valuationOf q) (1255)) (countLit q [-2]) (countLit q [-4, -5]) (count1254 q) 1 1 (meaningNeg2 q) (meaning1252 q) (meaning1255 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1252 = false ∨ valuationOf q 1255 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1252 = false ∨ valuation q 1255 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1253 = false ∨ valuationOf q 1256 = true := by
  have hs : count1254 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1253)) (literal (valuationOf q) (1256)) (countLit q [-2]) (countLit q [-4, -5]) (count1254 q) 1 2 (meaningNeg2 q) (meaning1253 q) (meaning1256 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1253 = false ∨ valuationOf q 1256 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1253 = false ∨ valuation q 1256 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1257)) (countLit q [-10]) (countLit q [-12]) (count1257 q) 1 (meaningNeg12 q) (meaning1257 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1257 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1257)) (countLit q [-10]) (countLit q [-12]) (count1257 q) 1 (meaningNeg10 q) (meaning1257 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1257 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 1257 = false ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-7]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-10, -12])
  have hm := merge_right (literal (valuationOf q) (1257)) (literal (valuationOf q) (1259)) (countLit q [-7]) (countLit q [-10, -12]) (count1259 q) 1 (meaning1257 q) (meaning1259 q) hs
  change valuationOf q 1257 = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 1257 = false ∨ valuation q 1259 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-7]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-10, -12])
  have hm := merge_left (literal (valuationOf q) (-7)) (literal (valuationOf q) (1259)) (countLit q [-7]) (countLit q [-10, -12]) (count1259 q) 1 (meaningNeg7 q) (meaning1259 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1259 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 1259 = false ∨ valuationOf q 1262 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -5]) + (countLit q [-7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-7, -10, -12])
  have hm := merge_right (literal (valuationOf q) (1259)) (literal (valuationOf q) (1262)) (countLit q [-2, -4, -5]) (countLit q [-7, -10, -12]) (count1262 q) 1 (meaning1259 q) (meaning1262 q) hs
  change valuationOf q 1259 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 1259 = false ∨ valuation q 1262 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1262 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -5]) + (countLit q [-7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-7, -10, -12])
  have hm := merge_left (literal (valuationOf q) (1254)) (literal (valuationOf q) (1262)) (countLit q [-2, -4, -5]) (countLit q [-7, -10, -12]) (count1262 q) 1 (meaning1254 q) (meaning1262 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1262 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1263 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -5]) + (countLit q [-7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1254)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1263)) (countLit q [-2, -4, -5]) (countLit q [-7, -10, -12]) (count1262 q) 1 1 (meaning1254 q) (meaning1259 q) (meaning1263 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1259 = false ∨ valuation q 1263 = true := counterClause189 (baseVal q)

theorem counterClause190 (q : Nat → Bool) : valuationOf q 1255 = false ∨ valuationOf q 1263 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -5]) + (countLit q [-7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-7, -10, -12])
  have hm := merge_left (literal (valuationOf q) (1255)) (literal (valuationOf q) (1263)) (countLit q [-2, -4, -5]) (countLit q [-7, -10, -12]) (count1262 q) 2 (meaning1255 q) (meaning1263 q) hs
  change valuationOf q 1255 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 1255 = false ∨ valuation q 1263 = true := counterClause190 (baseVal q)

theorem counterClause191 (q : Nat → Bool) : valuationOf q 1255 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1264 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -5]) + (countLit q [-7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1255)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1264)) (countLit q [-2, -4, -5]) (countLit q [-7, -10, -12]) (count1262 q) 2 1 (meaning1255 q) (meaning1259 q) (meaning1264 q) hs
  change valuationOf q 1255 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 1255 = false ∨ valuation q 1259 = false ∨ valuation q 1264 = true := counterClause191 (baseVal q)

theorem counterClause192 (q : Nat → Bool) : valuationOf q 1256 = false ∨ valuationOf q 1264 = true := by
  have hs : count1262 q = (countLit q [-2, -4, -5]) + (countLit q [-7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-7, -10, -12])
  have hm := merge_left (literal (valuationOf q) (1256)) (literal (valuationOf q) (1264)) (countLit q [-2, -4, -5]) (countLit q [-7, -10, -12]) (count1262 q) 3 (meaning1256 q) (meaning1264 q) hs
  change valuationOf q 1256 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 1256 = false ∨ valuation q 1264 = true := counterClause192 (baseVal q)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E246.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112246
