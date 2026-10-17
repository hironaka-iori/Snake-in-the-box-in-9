import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 382 = false ∨ valuationOf q 384 = true := by
  have hs : count383 q = (countLit q [180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_right (literal (valuationOf q) (382)) (literal (valuationOf q) (384)) (countLit q [180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) (count383 q) 2 (meaning382 q) (meaning384 q) hs
  change valuationOf q 382 = false ∨ valuationOf q 384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 382 = false ∨ valuation q 384 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_left (literal (valuationOf q) (367)) (literal (valuationOf q) (383)) (countLit q [180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) (count383 q) 1 (meaning367 q) (meaning383 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 383 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 381 = false ∨ valuationOf q 384 = true := by
  have hs : count383 q = (countLit q [180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_two (literal (valuationOf q) (367)) (literal (valuationOf q) (381)) (literal (valuationOf q) (384)) (countLit q [180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) (count383 q) 1 1 (meaning367 q) (meaning381 q) (meaning384 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 381 = false ∨ valuationOf q 384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 381 = false ∨ valuation q 384 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 368 = false ∨ valuationOf q 384 = true := by
  have hs : count383 q = (countLit q [180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_left (literal (valuationOf q) (368)) (literal (valuationOf q) (384)) (countLit q [180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) (count383 q) 2 (meaning368 q) (meaning384 q) hs
  change valuationOf q 368 = false ∨ valuationOf q 384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 368 = false ∨ valuation q 384 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_left (literal (valuationOf q) (197)) (literal (valuationOf q) (385)) (countLit q [197]) (countLit q [198]) (count385 q) 1 (meaning197 q) (meaning385 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 385 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197, 198])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [196]) (countLit q [197, 198]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197, 198])
  have hm := merge_left (literal (valuationOf q) (196)) (literal (valuationOf q) (387)) (countLit q [196]) (countLit q [197, 198]) (count387 q) 1 (meaning196 q) (meaning387 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 387 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197, 198])
  have hm := merge_two (literal (valuationOf q) (196)) (literal (valuationOf q) (385)) (literal (valuationOf q) (388)) (countLit q [196]) (countLit q [197, 198]) (count387 q) 1 1 (meaning196 q) (meaning385 q) (meaning388 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 385 = false ∨ valuation q 388 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 199 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [199]) + (countLit q [200]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200])
  have hm := merge_left (literal (valuationOf q) (199)) (literal (valuationOf q) (389)) (countLit q [199]) (countLit q [200]) (count389 q) 1 (meaning199 q) (meaning389 q) hs
  change valuationOf q 199 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 389 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [201]) + (countLit q [202]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202])
  have hm := merge_left (literal (valuationOf q) (201)) (literal (valuationOf q) (391)) (countLit q [201]) (countLit q [202]) (count391 q) 1 (meaning201 q) (meaning391 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 391 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [199, 200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [199, 200]) (l₂ := [201, 202])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [199, 200]) (countLit q [201, 202]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [199, 200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [199, 200]) (l₂ := [201, 202])
  have hm := merge_left (literal (valuationOf q) (389)) (literal (valuationOf q) (393)) (countLit q [199, 200]) (countLit q [201, 202]) (count393 q) 1 (meaning389 q) (meaning393 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 393 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [196, 197, 198]) + (countLit q [199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198]) (l₂ := [199, 200, 201, 202])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [196, 197, 198]) (countLit q [199, 200, 201, 202]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [196, 197, 198]) + (countLit q [199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198]) (l₂ := [199, 200, 201, 202])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (395)) (countLit q [196, 197, 198]) (countLit q [199, 200, 201, 202]) (count395 q) 1 (meaning387 q) (meaning395 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 395 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 393 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [196, 197, 198]) + (countLit q [199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198]) (l₂ := [199, 200, 201, 202])
  have hm := merge_two (literal (valuationOf q) (387)) (literal (valuationOf q) (393)) (literal (valuationOf q) (396)) (countLit q [196, 197, 198]) (countLit q [199, 200, 201, 202]) (count395 q) 1 1 (meaning387 q) (meaning393 q) (meaning396 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 393 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 393 = false ∨ valuation q 396 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [196, 197, 198]) + (countLit q [199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198]) (l₂ := [199, 200, 201, 202])
  have hm := merge_left (literal (valuationOf q) (388)) (literal (valuationOf q) (396)) (countLit q [196, 197, 198]) (countLit q [199, 200, 201, 202]) (count395 q) 2 (meaning388 q) (meaning396 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 396 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 205 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [205]) + (countLit q [206]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206])
  have hm := merge_left (literal (valuationOf q) (205)) (literal (valuationOf q) (399)) (countLit q [205]) (countLit q [206]) (count399 q) 1 (meaning205 q) (meaning399 q) hs
  change valuationOf q 205 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 399 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [203, 204]) + (countLit q [205, 206]) := List.countP_append (p := literal q) (l₁ := [203, 204]) (l₂ := [205, 206])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [203, 204]) (countLit q [205, 206]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [207]) + (countLit q [208]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208])
  have hm := merge_right (literal (valuationOf q) (208)) (literal (valuationOf q) (403)) (countLit q [207]) (countLit q [208]) (count403 q) 1 (meaning208 q) (meaning403 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 403 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_left (literal (valuationOf q) (209)) (literal (valuationOf q) (405)) (countLit q [209]) (countLit q [210]) (count405 q) 1 (meaning209 q) (meaning405 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 405 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [207, 208]) + (countLit q [209, 210]) := List.countP_append (p := literal q) (l₁ := [207, 208]) (l₂ := [209, 210])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [207, 208]) (countLit q [209, 210]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [207, 208]) + (countLit q [209, 210]) := List.countP_append (p := literal q) (l₁ := [207, 208]) (l₂ := [209, 210])
  have hm := merge_left (literal (valuationOf q) (403)) (literal (valuationOf q) (407)) (countLit q [207, 208]) (countLit q [209, 210]) (count407 q) 1 (meaning403 q) (meaning407 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 407 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [203, 204, 205, 206]) + (countLit q [207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [203, 204, 205, 206]) (l₂ := [207, 208, 209, 210])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [203, 204, 205, 206]) (countLit q [207, 208, 209, 210]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [203, 204, 205, 206]) + (countLit q [207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [203, 204, 205, 206]) (l₂ := [207, 208, 209, 210])
  have hm := merge_left (literal (valuationOf q) (401)) (literal (valuationOf q) (409)) (countLit q [203, 204, 205, 206]) (countLit q [207, 208, 209, 210]) (count409 q) 1 (meaning401 q) (meaning409 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 409 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [196, 197, 198, 199, 200, 201, 202]) + (countLit q [203, 204, 205, 206, 207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201, 202]) (l₂ := [203, 204, 205, 206, 207, 208, 209, 210])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [196, 197, 198, 199, 200, 201, 202]) (countLit q [203, 204, 205, 206, 207, 208, 209, 210]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [196, 197, 198, 199, 200, 201, 202]) + (countLit q [203, 204, 205, 206, 207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201, 202]) (l₂ := [203, 204, 205, 206, 207, 208, 209, 210])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (411)) (countLit q [196, 197, 198, 199, 200, 201, 202]) (countLit q [203, 204, 205, 206, 207, 208, 209, 210]) (count411 q) 1 (meaning395 q) (meaning411 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 411 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [196, 197, 198, 199, 200, 201, 202]) + (countLit q [203, 204, 205, 206, 207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201, 202]) (l₂ := [203, 204, 205, 206, 207, 208, 209, 210])
  have hm := merge_two (literal (valuationOf q) (395)) (literal (valuationOf q) (409)) (literal (valuationOf q) (412)) (countLit q [196, 197, 198, 199, 200, 201, 202]) (countLit q [203, 204, 205, 206, 207, 208, 209, 210]) (count411 q) 1 1 (meaning395 q) (meaning409 q) (meaning412 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 409 = false ∨ valuation q 412 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 396 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [196, 197, 198, 199, 200, 201, 202]) + (countLit q [203, 204, 205, 206, 207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201, 202]) (l₂ := [203, 204, 205, 206, 207, 208, 209, 210])
  have hm := merge_left (literal (valuationOf q) (396)) (literal (valuationOf q) (412)) (countLit q [196, 197, 198, 199, 200, 201, 202]) (countLit q [203, 204, 205, 206, 207, 208, 209, 210]) (count411 q) 2 (meaning396 q) (meaning412 q) hs
  change valuationOf q 396 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 396 = false ∨ valuation q 412 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210])
  have hm := merge_right (literal (valuationOf q) (411)) (literal (valuationOf q) (413)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) (count413 q) 1 (meaning411 q) (meaning413 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 413 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 412 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210])
  have hm := merge_right (literal (valuationOf q) (412)) (literal (valuationOf q) (414)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) (count413 q) 2 (meaning412 q) (meaning414 q) hs
  change valuationOf q 412 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 412 = false ∨ valuation q 414 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210])
  have hm := merge_left (literal (valuationOf q) (383)) (literal (valuationOf q) (413)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) (count413 q) 1 (meaning383 q) (meaning413 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 413 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E004.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112004
