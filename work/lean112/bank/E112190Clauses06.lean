import E112190Semantics
import B112E190Inputs
namespace Snake9.Regrowth.E112190
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause193 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197, 198])
  have hm := merge_left (literal (valuationOf q) (196)) (literal (valuationOf q) (385)) (countLit q [196]) (countLit q [197, 198]) (count385 q) 1 (meaning196 q) (meaning385 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 385 = true := counterClause193 (baseVal q)

theorem counterClause194 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [196, 197, 198]) + (countLit q [199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198]) (l₂ := [199, 200, 201, 202])
  have hm := merge_left (literal (valuationOf q) (385)) (literal (valuationOf q) (393)) (countLit q [196, 197, 198]) (countLit q [199, 200, 201, 202]) (count393 q) 1 (meaning385 q) (meaning393 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 393 = true := counterClause194 (baseVal q)

theorem counterClause195 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause195 (baseVal q)

theorem counterClause196 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (395)) (countLit q [190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202]) (count395 q) 1 (meaning381 q) (meaning395 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 395 = true := counterClause196 (baseVal q)

theorem counterClause197 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [206]) + (countLit q [207]) := List.countP_append (p := literal q) (l₁ := [206]) (l₂ := [207])
  have hm := merge_left (literal (valuationOf q) (206)) (literal (valuationOf q) (401)) (countLit q [206]) (countLit q [207]) (count401 q) 1 (meaning206 q) (meaning401 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 401 = true := counterClause197 (baseVal q)

theorem counterClause198 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [206, 207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [206, 207]) (l₂ := [208, 209])
  have hm := merge_left (literal (valuationOf q) (401)) (literal (valuationOf q) (405)) (countLit q [206, 207]) (countLit q [208, 209]) (count405 q) 1 (meaning401 q) (meaning405 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 405 = true := counterClause198 (baseVal q)

theorem counterClause199 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [203, 204, 205]) + (countLit q [206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [203, 204, 205]) (l₂ := [206, 207, 208, 209])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [203, 204, 205]) (countLit q [206, 207, 208, 209]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause199 (baseVal q)

theorem counterClause200 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216])
  have hm := merge_left (literal (valuationOf q) (407)) (literal (valuationOf q) (421)) (countLit q [203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216]) (count421 q) 1 (meaning407 q) (meaning421 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 421 = true := counterClause200 (baseVal q)

theorem counterClause201 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) + (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (l₂ := [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_right (literal (valuationOf q) (421)) (literal (valuationOf q) (423)) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count423 q) 1 (meaning421 q) (meaning423 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = true := counterClause201 (baseVal q)

theorem counterClause202 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) + (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (l₂ := [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (423)) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (countLit q [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count423 q) 1 (meaning395 q) (meaning423 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 423 = true := counterClause202 (baseVal q)

theorem counterClause203 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause203 (baseVal q)

theorem counterClause204 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_left (literal (valuationOf q) (371)) (literal (valuationOf q) (425)) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count425 q) 1 (meaning371 q) (meaning425 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 425 = true := counterClause204 (baseVal q)

theorem counterClause205 (q : Nat → Bool) : valuationOf q 372 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_left (literal (valuationOf q) (372)) (literal (valuationOf q) (426)) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count425 q) 2 (meaning372 q) (meaning426 q) hs
  change valuationOf q 372 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 372 = false ∨ valuation q 426 = true := counterClause205 (baseVal q)

theorem counterClause206 (q : Nat → Bool) : valuationOf q 426 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_right (literal (valuationOf q) (426)) (literal (valuationOf q) (428)) (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count427 q) 2 (meaning426 q) (meaning428 q) hs
  change valuationOf q 426 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 426 = false ∨ valuation q 428 = true := counterClause206 (baseVal q)

theorem counterClause207 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_two (literal (valuationOf q) (319)) (literal (valuationOf q) (425)) (literal (valuationOf q) (428)) (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count427 q) 1 1 (meaning319 q) (meaning425 q) (meaning428 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 425 = false ∨ valuation q 428 = true := counterClause207 (baseVal q)

theorem counterClause208 (q : Nat → Bool) : valuationOf q 320 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) := List.countP_append (p := literal q) (l₁ := [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216])
  have hm := merge_left (literal (valuationOf q) (320)) (literal (valuationOf q) (428)) (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]) (count427 q) 2 (meaning320 q) (meaning428 q) hs
  change valuationOf q 320 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 320 = false ∨ valuation q 428 = true := counterClause208 (baseVal q)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 428 = false := by
  rw [value428]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count427 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause210 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1289 = true := by
  have hs : count1289 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1289)) (countLit q [-4]) (countLit q [-5]) (count1289 q) 1 (meaningNeg4 q) (meaning1289 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1289 = true := counterClause210 (baseVal q)

theorem counterClause211 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1291 = true := by
  have hs : count1291 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1289)) (literal (valuationOf q) (1291)) (countLit q [-2]) (countLit q [-4, -5]) (count1291 q) 1 (meaning1289 q) (meaning1291 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1291 = true := counterClause211 (baseVal q)

theorem counterClause212 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1291 = true := by
  have hs : count1291 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1291)) (countLit q [-2]) (countLit q [-4, -5]) (count1291 q) 1 (meaningNeg2 q) (meaning1291 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1291 = true := counterClause212 (baseVal q)

theorem counterClause213 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1294 = true := by
  have hs : count1294 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1294)) (countLit q [-10]) (countLit q [-12]) (count1294 q) 1 (meaningNeg12 q) (meaning1294 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1294 = true := counterClause213 (baseVal q)

theorem counterClause214 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1294 = true := by
  have hs : count1294 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1294)) (countLit q [-10]) (countLit q [-12]) (count1294 q) 1 (meaningNeg10 q) (meaning1294 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1294 = true := counterClause214 (baseVal q)

theorem counterClause215 (q : Nat → Bool) : valuationOf q 1294 = false ∨ valuationOf q 1296 = true := by
  have hs : count1296 q = (countLit q [-7]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-10, -12])
  have hm := merge_right (literal (valuationOf q) (1294)) (literal (valuationOf q) (1296)) (countLit q [-7]) (countLit q [-10, -12]) (count1296 q) 1 (meaning1294 q) (meaning1296 q) hs
  change valuationOf q 1294 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 1294 = false ∨ valuation q 1296 = true := counterClause215 (baseVal q)

theorem counterClause216 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1296 = true := by
  have hs : count1296 q = (countLit q [-7]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-10, -12])
  have hm := merge_left (literal (valuationOf q) (-7)) (literal (valuationOf q) (1296)) (countLit q [-7]) (countLit q [-10, -12]) (count1296 q) 1 (meaningNeg7 q) (meaning1296 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1296 = true := counterClause216 (baseVal q)

theorem counterClause217 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-2, -4, -5]) + (countLit q [-7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-7, -10, -12])
  have hm := merge_right (literal (valuationOf q) (1296)) (literal (valuationOf q) (1299)) (countLit q [-2, -4, -5]) (countLit q [-7, -10, -12]) (count1299 q) 1 (meaning1296 q) (meaning1299 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1299 = true := counterClause217 (baseVal q)

theorem counterClause218 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-2, -4, -5]) + (countLit q [-7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-7, -10, -12])
  have hm := merge_left (literal (valuationOf q) (1291)) (literal (valuationOf q) (1299)) (countLit q [-2, -4, -5]) (countLit q [-7, -10, -12]) (count1299 q) 1 (meaning1291 q) (meaning1299 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1299 = true := counterClause218 (baseVal q)

theorem counterClause219 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1300 = true := by
  have hs : count1299 q = (countLit q [-2, -4, -5]) + (countLit q [-7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1300)) (countLit q [-2, -4, -5]) (countLit q [-7, -10, -12]) (count1299 q) 1 1 (meaning1291 q) (meaning1296 q) (meaning1300 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1296 = false ∨ valuation q 1300 = true := counterClause219 (baseVal q)

theorem counterClause220 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1305 = true := by
  have hs : count1305 q = (countLit q [-15]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1305)) (countLit q [-15]) (countLit q [-19]) (count1305 q) 1 (meaningNeg19 q) (meaning1305 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1305 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1305 = true := counterClause220 (baseVal q)

theorem counterClause221 (q : Nat → Bool) : valuationOf q 1305 = false ∨ valuationOf q 1307 = true := by
  have hs : count1307 q = (countLit q [-13]) + (countLit q [-15, -19]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -19])
  have hm := merge_right (literal (valuationOf q) (1305)) (literal (valuationOf q) (1307)) (countLit q [-13]) (countLit q [-15, -19]) (count1307 q) 1 (meaning1305 q) (meaning1307 q) hs
  change valuationOf q 1305 = false ∨ valuationOf q 1307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 1305 = false ∨ valuation q 1307 = true := counterClause221 (baseVal q)

theorem counterClause222 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1307 = true := by
  have hs : count1307 q = (countLit q [-13]) + (countLit q [-15, -19]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -19])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1307)) (countLit q [-13]) (countLit q [-15, -19]) (count1307 q) 1 (meaningNeg13 q) (meaning1307 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1307 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1307 = true := counterClause222 (baseVal q)

theorem counterClause223 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1310 = true := by
  have hs : count1310 q = (countLit q [-21]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1310)) (countLit q [-21]) (countLit q [-24]) (count1310 q) 1 (meaningNeg24 q) (meaning1310 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1310 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1310 = true := counterClause223 (baseVal q)

theorem counterClause224 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1310 = true := by
  have hs : count1310 q = (countLit q [-21]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1310)) (countLit q [-21]) (countLit q [-24]) (count1310 q) 1 (meaningNeg21 q) (meaning1310 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1310 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1310 = true := counterClause224 (baseVal q)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E190.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112190
