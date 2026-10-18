import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (378)) (literal (valuationOf q) (380)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (count379 q) 2 (meaning378 q) (meaning380 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 380 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (379)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (count379 q) 1 (meaning315 q) (meaning379 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 379 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 377 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_two (literal (valuationOf q) (315)) (literal (valuationOf q) (377)) (literal (valuationOf q) (380)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (count379 q) 1 1 (meaning315 q) (meaning377 q) (meaning380 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 377 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 377 = false ∨ valuation q 380 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 316 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (316)) (literal (valuationOf q) (380)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (count379 q) 2 (meaning316 q) (meaning380 q) hs
  change valuationOf q 316 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 316 = false ∨ valuation q 380 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 193 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [192]) + (countLit q [193]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193])
  have hm := merge_right (literal (valuationOf q) (193)) (literal (valuationOf q) (381)) (countLit q [192]) (countLit q [193]) (count381 q) 1 (meaning193 q) (meaning381 q) hs
  change valuationOf q 193 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 381 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [192, 193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [192, 193]) (l₂ := [194, 195])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (385)) (countLit q [192, 193]) (countLit q [194, 195]) (count385 q) 1 (meaning381 q) (meaning385 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 385 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_right (literal (valuationOf q) (197)) (literal (valuationOf q) (387)) (countLit q [196]) (countLit q [197]) (count387 q) 1 (meaning197 q) (meaning387 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 387 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_left (literal (valuationOf q) (196)) (literal (valuationOf q) (387)) (countLit q [196]) (countLit q [197]) (count387 q) 1 (meaning196 q) (meaning387 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 387 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 197 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_two (literal (valuationOf q) (196)) (literal (valuationOf q) (197)) (literal (valuationOf q) (388)) (countLit q [196]) (countLit q [197]) (count387 q) 1 1 (meaning196 q) (meaning197 q) (meaning388 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 197 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 197 = false ∨ valuation q 388 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [196, 197]) + (countLit q [198, 199]) := List.countP_append (p := literal q) (l₁ := [196, 197]) (l₂ := [198, 199])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (391)) (countLit q [196, 197]) (countLit q [198, 199]) (count391 q) 1 (meaning387 q) (meaning391 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 391 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [196, 197]) + (countLit q [198, 199]) := List.countP_append (p := literal q) (l₁ := [196, 197]) (l₂ := [198, 199])
  have hm := merge_left (literal (valuationOf q) (388)) (literal (valuationOf q) (392)) (countLit q [196, 197]) (countLit q [198, 199]) (count391 q) 2 (meaning388 q) (meaning392 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 392 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [192, 193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [192, 193, 194, 195]) (countLit q [196, 197, 198, 199]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 392 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [192, 193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_right (literal (valuationOf q) (392)) (literal (valuationOf q) (394)) (countLit q [192, 193, 194, 195]) (countLit q [196, 197, 198, 199]) (count393 q) 2 (meaning392 q) (meaning394 q) hs
  change valuationOf q 392 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 392 = false ∨ valuation q 394 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [192, 193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_left (literal (valuationOf q) (385)) (literal (valuationOf q) (393)) (countLit q [192, 193, 194, 195]) (countLit q [196, 197, 198, 199]) (count393 q) 1 (meaning385 q) (meaning393 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 393 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 391 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [192, 193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_two (literal (valuationOf q) (385)) (literal (valuationOf q) (391)) (literal (valuationOf q) (394)) (countLit q [192, 193, 194, 195]) (countLit q [196, 197, 198, 199]) (count393 q) 1 1 (meaning385 q) (meaning391 q) (meaning394 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 391 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 391 = false ∨ valuation q 394 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 205 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [204]) + (countLit q [205]) := List.countP_append (p := literal q) (l₁ := [204]) (l₂ := [205])
  have hm := merge_right (literal (valuationOf q) (205)) (literal (valuationOf q) (401)) (countLit q [204]) (countLit q [205]) (count401 q) 1 (meaning205 q) (meaning401 q) hs
  change valuationOf q 205 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 401 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [206]) + (countLit q [207]) := List.countP_append (p := literal q) (l₁ := [206]) (l₂ := [207])
  have hm := merge_left (literal (valuationOf q) (206)) (literal (valuationOf q) (403)) (countLit q [206]) (countLit q [207]) (count403 q) 1 (meaning206 q) (meaning403 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 403 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [204, 205]) + (countLit q [206, 207]) := List.countP_append (p := literal q) (l₁ := [204, 205]) (l₂ := [206, 207])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [204, 205]) (countLit q [206, 207]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [204, 205]) + (countLit q [206, 207]) := List.countP_append (p := literal q) (l₁ := [204, 205]) (l₂ := [206, 207])
  have hm := merge_left (literal (valuationOf q) (401)) (literal (valuationOf q) (405)) (countLit q [204, 205]) (countLit q [206, 207]) (count405 q) 1 (meaning401 q) (meaning405 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 405 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [200, 201, 202, 203]) + (countLit q [204, 205, 206, 207]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202, 203]) (l₂ := [204, 205, 206, 207])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [200, 201, 202, 203]) (countLit q [204, 205, 206, 207]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207])
  have hm := merge_left (literal (valuationOf q) (393)) (literal (valuationOf q) (409)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207]) (count409 q) 1 (meaning393 q) (meaning409 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 409 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207])
  have hm := merge_two (literal (valuationOf q) (393)) (literal (valuationOf q) (407)) (literal (valuationOf q) (410)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207]) (count409 q) 1 1 (meaning393 q) (meaning407 q) (meaning410 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 407 = false ∨ valuation q 410 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 394 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207])
  have hm := merge_left (literal (valuationOf q) (394)) (literal (valuationOf q) (410)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207]) (count409 q) 2 (meaning394 q) (meaning410 q) hs
  change valuationOf q 394 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 394 = false ∨ valuation q 410 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (417)) (countLit q [212]) (countLit q [213]) (count417 q) 1 (meaning213 q) (meaning417 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 417 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [212, 213]) + (countLit q [214, 216]) := List.countP_append (p := literal q) (l₁ := [212, 213]) (l₂ := [214, 216])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (421)) (countLit q [212, 213]) (countLit q [214, 216]) (count421 q) 1 (meaning417 q) (meaning421 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 421 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [208, 209, 210, 211]) + (countLit q [212, 213, 214, 216]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211]) (l₂ := [212, 213, 214, 216])
  have hm := merge_right (literal (valuationOf q) (421)) (literal (valuationOf q) (423)) (countLit q [208, 209, 210, 211]) (countLit q [212, 213, 214, 216]) (count423 q) 1 (meaning421 q) (meaning423 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 218 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_right (literal (valuationOf q) (218)) (literal (valuationOf q) (425)) (countLit q [217]) (countLit q [218]) (count425 q) 1 (meaning218 q) (meaning425 q) hs
  change valuationOf q 218 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 425 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [219]) + (countLit q [220]) := List.countP_append (p := literal q) (l₁ := [219]) (l₂ := [220])
  have hm := merge_left (literal (valuationOf q) (219)) (literal (valuationOf q) (427)) (countLit q [219]) (countLit q [220]) (count427 q) 1 (meaning219 q) (meaning427 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 427 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [217, 218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [217, 218]) (l₂ := [219, 220])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [217, 218]) (countLit q [219, 220]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [217, 218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [217, 218]) (l₂ := [219, 220])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (429)) (countLit q [217, 218]) (countLit q [219, 220]) (count429 q) 1 (meaning425 q) (meaning429 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 429 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [217, 218, 219, 220]) + (countLit q [221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [217, 218, 219, 220]) (l₂ := [221, 222, 223, 224])
  have hm := merge_left (literal (valuationOf q) (429)) (literal (valuationOf q) (437)) (countLit q [217, 218, 219, 220]) (countLit q [221, 222, 223, 224]) (count437 q) 1 (meaning429 q) (meaning437 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 437 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E036.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112036
