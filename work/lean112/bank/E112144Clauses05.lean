import E112144Semantics
import B112E144Inputs
namespace Snake9.Regrowth.E112144
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause161 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (415)) (countLit q [185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 (meaning387 q) (meaning415 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 415 = true := counterClause161 (baseVal q)

theorem counterClause162 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) + (countLit q [185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) (l₂ := [185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (363)) (literal (valuationOf q) (417)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) (countLit q [185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 (meaning363 q) (meaning417 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 417 = true := counterClause162 (baseVal q)

theorem counterClause163 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) + (countLit q [185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) (l₂ := [185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (363)) (literal (valuationOf q) (415)) (literal (valuationOf q) (418)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) (countLit q [185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 1 (meaning363 q) (meaning415 q) (meaning418 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 415 = false ∨ valuation q 418 = true := counterClause163 (baseVal q)

theorem counterClause164 (q : Nat → Bool) : valuationOf q 364 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) + (countLit q [185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) (l₂ := [185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (364)) (literal (valuationOf q) (418)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) (countLit q [185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 2 (meaning364 q) (meaning418 q) hs
  change valuationOf q 364 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 364 = false ∨ valuation q 418 = true := counterClause164 (baseVal q)

theorem counterClause165 (q : Nat → Bool) : valuationOf q 418 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (418)) (literal (valuationOf q) (420)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count419 q) 2 (meaning418 q) (meaning420 q) hs
  change valuationOf q 418 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 420 = true := counterClause165 (baseVal q)

theorem counterClause166 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 417 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (313)) (literal (valuationOf q) (417)) (literal (valuationOf q) (420)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count419 q) 1 1 (meaning313 q) (meaning417 q) (meaning420 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 417 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 417 = false ∨ valuation q 420 = true := counterClause166 (baseVal q)

theorem counterClause167 (q : Nat → Bool) : valuationOf q 314 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (314)) (literal (valuationOf q) (420)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count419 q) 2 (meaning314 q) (meaning420 q) hs
  change valuationOf q 314 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 314 = false ∨ valuation q 420 = true := counterClause167 (baseVal q)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 420 = false := by
  rw [value420]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count419 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause169 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1252 = true := by
  have hs : count1252 q = (countLit q [-2]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1252)) (countLit q [-2]) (countLit q [-5]) (count1252 q) 1 (meaningNeg5 q) (meaning1252 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1252 = true := counterClause169 (baseVal q)

theorem counterClause170 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1252 = true := by
  have hs : count1252 q = (countLit q [-2]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1252)) (countLit q [-2]) (countLit q [-5]) (count1252 q) 1 (meaningNeg2 q) (meaning1252 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1252 = true := counterClause170 (baseVal q)

theorem counterClause171 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1253 = true := by
  have hs : count1252 q = (countLit q [-2]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1253)) (countLit q [-2]) (countLit q [-5]) (count1252 q) 1 1 (meaningNeg2 q) (meaningNeg5 q) (meaning1253 q) hs
  change (! (valuationOf q 2)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 5 = true ∨ valuation q 1253 = true := counterClause171 (baseVal q)

theorem counterClause172 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1254 = true := by
  have hs : count1254 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_right (literal (valuationOf q) (1252)) (literal (valuationOf q) (1254)) (countLit q [-1]) (countLit q [-2, -5]) (count1254 q) 1 (meaning1252 q) (meaning1254 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1254 = true := counterClause172 (baseVal q)

theorem counterClause173 (q : Nat → Bool) : valuationOf q 1253 = false ∨ valuationOf q 1255 = true := by
  have hs : count1254 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_right (literal (valuationOf q) (1253)) (literal (valuationOf q) (1255)) (countLit q [-1]) (countLit q [-2, -5]) (count1254 q) 2 (meaning1253 q) (meaning1255 q) hs
  change valuationOf q 1253 = false ∨ valuationOf q 1255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 1253 = false ∨ valuation q 1255 = true := counterClause173 (baseVal q)

theorem counterClause174 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 1254 = true := by
  have hs : count1254 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (1254)) (countLit q [-1]) (countLit q [-2, -5]) (count1254 q) 1 (meaningNeg1 q) (meaning1254 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 1254 = true := counterClause174 (baseVal q)

theorem counterClause175 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 1252 = false ∨ valuationOf q 1255 = true := by
  have hs : count1254 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (1252)) (literal (valuationOf q) (1255)) (countLit q [-1]) (countLit q [-2, -5]) (count1254 q) 1 1 (meaningNeg1 q) (meaning1252 q) (meaning1255 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 1252 = false ∨ valuationOf q 1255 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 1252 = false ∨ valuation q 1255 = true := counterClause175 (baseVal q)

theorem counterClause176 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 1253 = false ∨ valuationOf q 1256 = true := by
  have hs : count1254 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (1253)) (literal (valuationOf q) (1256)) (countLit q [-1]) (countLit q [-2, -5]) (count1254 q) 1 2 (meaningNeg1 q) (meaning1253 q) (meaning1256 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 1253 = false ∨ valuationOf q 1256 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 1253 = false ∨ valuation q 1256 = true := counterClause176 (baseVal q)

theorem counterClause177 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (1257)) (countLit q [-9]) (countLit q [-11]) (count1257 q) 1 (meaningNeg11 q) (meaning1257 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1257 = true := counterClause177 (baseVal q)

theorem counterClause178 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (1257)) (countLit q [-9]) (countLit q [-11]) (count1257 q) 1 (meaningNeg9 q) (meaning1257 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1257 = true := counterClause178 (baseVal q)

theorem counterClause179 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 11 = true ∨ valuationOf q 1258 = true := by
  have hs : count1257 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-11)) (literal (valuationOf q) (1258)) (countLit q [-9]) (countLit q [-11]) (count1257 q) 1 1 (meaningNeg9 q) (meaningNeg11 q) (meaning1258 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 11)) = false ∨ valuationOf q 1258 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 11 = true ∨ valuation q 1258 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 1257 = false ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-7]) + (countLit q [-9, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-9, -11])
  have hm := merge_right (literal (valuationOf q) (1257)) (literal (valuationOf q) (1259)) (countLit q [-7]) (countLit q [-9, -11]) (count1259 q) 1 (meaning1257 q) (meaning1259 q) hs
  change valuationOf q 1257 = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 1257 = false ∨ valuation q 1259 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 1258 = false ∨ valuationOf q 1260 = true := by
  have hs : count1259 q = (countLit q [-7]) + (countLit q [-9, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-9, -11])
  have hm := merge_right (literal (valuationOf q) (1258)) (literal (valuationOf q) (1260)) (countLit q [-7]) (countLit q [-9, -11]) (count1259 q) 2 (meaning1258 q) (meaning1260 q) hs
  change valuationOf q 1258 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 1258 = false ∨ valuation q 1260 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-7]) + (countLit q [-9, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-9, -11])
  have hm := merge_left (literal (valuationOf q) (-7)) (literal (valuationOf q) (1259)) (countLit q [-7]) (countLit q [-9, -11]) (count1259 q) 1 (meaningNeg7 q) (meaning1259 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1259 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1257 = false ∨ valuationOf q 1260 = true := by
  have hs : count1259 q = (countLit q [-7]) + (countLit q [-9, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-9, -11])
  have hm := merge_two (literal (valuationOf q) (-7)) (literal (valuationOf q) (1257)) (literal (valuationOf q) (1260)) (countLit q [-7]) (countLit q [-9, -11]) (count1259 q) 1 1 (meaningNeg7 q) (meaning1257 q) (meaning1260 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1257 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1257 = false ∨ valuation q 1260 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1258 = false ∨ valuationOf q 1261 = true := by
  have hs : count1259 q = (countLit q [-7]) + (countLit q [-9, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-9, -11])
  have hm := merge_two (literal (valuationOf q) (-7)) (literal (valuationOf q) (1258)) (literal (valuationOf q) (1261)) (countLit q [-7]) (countLit q [-9, -11]) (count1259 q) 1 2 (meaningNeg7 q) (meaning1258 q) (meaning1261 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1258 = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1258 = false ∨ valuation q 1261 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 1259 = false ∨ valuationOf q 1262 = true := by
  have hs : count1262 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -9, -11])
  have hm := merge_right (literal (valuationOf q) (1259)) (literal (valuationOf q) (1262)) (countLit q [-1, -2, -5]) (countLit q [-7, -9, -11]) (count1262 q) 1 (meaning1259 q) (meaning1262 q) hs
  change valuationOf q 1259 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 1259 = false ∨ valuation q 1262 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 1260 = false ∨ valuationOf q 1263 = true := by
  have hs : count1262 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -9, -11])
  have hm := merge_right (literal (valuationOf q) (1260)) (literal (valuationOf q) (1263)) (countLit q [-1, -2, -5]) (countLit q [-7, -9, -11]) (count1262 q) 2 (meaning1260 q) (meaning1263 q) hs
  change valuationOf q 1260 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 1260 = false ∨ valuation q 1263 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 1261 = false ∨ valuationOf q 1264 = true := by
  have hs : count1262 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -9, -11])
  have hm := merge_right (literal (valuationOf q) (1261)) (literal (valuationOf q) (1264)) (countLit q [-1, -2, -5]) (countLit q [-7, -9, -11]) (count1262 q) 3 (meaning1261 q) (meaning1264 q) hs
  change valuationOf q 1261 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 1261 = false ∨ valuation q 1264 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1262 = true := by
  have hs : count1262 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -9, -11])
  have hm := merge_left (literal (valuationOf q) (1254)) (literal (valuationOf q) (1262)) (countLit q [-1, -2, -5]) (countLit q [-7, -9, -11]) (count1262 q) 1 (meaning1254 q) (meaning1262 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1262 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1263 = true := by
  have hs : count1262 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -9, -11])
  have hm := merge_two (literal (valuationOf q) (1254)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1263)) (countLit q [-1, -2, -5]) (countLit q [-7, -9, -11]) (count1262 q) 1 1 (meaning1254 q) (meaning1259 q) (meaning1263 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1259 = false ∨ valuation q 1263 = true := counterClause189 (baseVal q)

theorem counterClause190 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1264 = true := by
  have hs : count1262 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -9, -11])
  have hm := merge_two (literal (valuationOf q) (1254)) (literal (valuationOf q) (1260)) (literal (valuationOf q) (1264)) (countLit q [-1, -2, -5]) (countLit q [-7, -9, -11]) (count1262 q) 1 2 (meaning1254 q) (meaning1260 q) (meaning1264 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1260 = false ∨ valuation q 1264 = true := counterClause190 (baseVal q)

theorem counterClause191 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1265 = true := by
  have hs : count1262 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -9, -11])
  have hm := merge_two (literal (valuationOf q) (1254)) (literal (valuationOf q) (1261)) (literal (valuationOf q) (1265)) (countLit q [-1, -2, -5]) (countLit q [-7, -9, -11]) (count1262 q) 1 3 (meaning1254 q) (meaning1261 q) (meaning1265 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1261 = false ∨ valuation q 1265 = true := counterClause191 (baseVal q)

theorem counterClause192 (q : Nat → Bool) : valuationOf q 1255 = false ∨ valuationOf q 1263 = true := by
  have hs : count1262 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -9, -11])
  have hm := merge_left (literal (valuationOf q) (1255)) (literal (valuationOf q) (1263)) (countLit q [-1, -2, -5]) (countLit q [-7, -9, -11]) (count1262 q) 2 (meaning1255 q) (meaning1263 q) hs
  change valuationOf q 1255 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 1255 = false ∨ valuation q 1263 = true := counterClause192 (baseVal q)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E144.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112144
