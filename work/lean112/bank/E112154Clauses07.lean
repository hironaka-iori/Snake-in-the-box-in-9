import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [182]) + (countLit q [183]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183])
  have hm := merge_right (literal (valuationOf q) (183)) (literal (valuationOf q) (353)) (countLit q [182]) (countLit q [183]) (count353 q) 1 (meaning183 q) (meaning353 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 353 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 182 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [182]) + (countLit q [183]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183])
  have hm := merge_left (literal (valuationOf q) (182)) (literal (valuationOf q) (353)) (countLit q [182]) (countLit q [183]) (count353 q) 1 (meaning182 q) (meaning353 q) hs
  change valuationOf q 182 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 353 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182, 183])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [181]) (countLit q [182, 183]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [178, 179, 180]) + (countLit q [181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180]) (l₂ := [181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (355)) (literal (valuationOf q) (357)) (countLit q [178, 179, 180]) (countLit q [181, 182, 183]) (count357 q) 1 (meaning355 q) (meaning357 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 357 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [178, 179, 180]) + (countLit q [181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180]) (l₂ := [181, 182, 183])
  have hm := merge_left (literal (valuationOf q) (351)) (literal (valuationOf q) (357)) (countLit q [178, 179, 180]) (countLit q [181, 182, 183]) (count357 q) 1 (meaning351 q) (meaning357 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 357 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [187]) + (countLit q [188, 189]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188, 189])
  have hm := merge_left (literal (valuationOf q) (187)) (literal (valuationOf q) (365)) (countLit q [187]) (countLit q [188, 189]) (count365 q) 1 (meaning187 q) (meaning365 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 365 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [184, 185, 186]) + (countLit q [187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186]) (l₂ := [187, 188, 189])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [184, 185, 186]) (countLit q [187, 188, 189]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189])
  have hm := merge_right (literal (valuationOf q) (367)) (literal (valuationOf q) (369)) (countLit q [178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189]) (count369 q) 1 (meaning367 q) (meaning369 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 369 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189])
  have hm := merge_left (literal (valuationOf q) (357)) (literal (valuationOf q) (369)) (countLit q [178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189]) (count369 q) 1 (meaning357 q) (meaning369 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 369 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 190 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [190]) + (countLit q [191, 192]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191, 192])
  have hm := merge_left (literal (valuationOf q) (190)) (literal (valuationOf q) (373)) (countLit q [190]) (countLit q [191, 192]) (count373 q) 1 (meaning190 q) (meaning373 q) hs
  change valuationOf q 190 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 373 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 193 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194, 195])
  have hm := merge_left (literal (valuationOf q) (193)) (literal (valuationOf q) (377)) (countLit q [193]) (countLit q [194, 195]) (count377 q) 1 (meaning193 q) (meaning377 q) hs
  change valuationOf q 193 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 377 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [190, 191, 192]) + (countLit q [193, 194, 195]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192]) (l₂ := [193, 194, 195])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [190, 191, 192]) (countLit q [193, 194, 195]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [190, 191, 192]) + (countLit q [193, 194, 195]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192]) (l₂ := [193, 194, 195])
  have hm := merge_left (literal (valuationOf q) (373)) (literal (valuationOf q) (379)) (countLit q [190, 191, 192]) (countLit q [193, 194, 195]) (count379 q) 1 (meaning373 q) (meaning379 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 379 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_left (literal (valuationOf q) (197)) (literal (valuationOf q) (381)) (countLit q [197]) (countLit q [198]) (count381 q) 1 (meaning197 q) (meaning381 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 381 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197, 198])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [196]) (countLit q [197, 198]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [201]) + (countLit q [202]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202])
  have hm := merge_left (literal (valuationOf q) (201)) (literal (valuationOf q) (387)) (countLit q [201]) (countLit q [202]) (count387 q) 1 (meaning201 q) (meaning387 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 387 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [199, 200]) + (countLit q [201, 202]) := List.countP_append (p := literal q) (l₁ := [199, 200]) (l₂ := [201, 202])
  have hm := merge_right (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (countLit q [199, 200]) (countLit q [201, 202]) (count389 q) 1 (meaning387 q) (meaning389 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [196, 197, 198]) + (countLit q [199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198]) (l₂ := [199, 200, 201, 202])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [196, 197, 198]) (countLit q [199, 200, 201, 202]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [196, 197, 198]) + (countLit q [199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198]) (l₂ := [199, 200, 201, 202])
  have hm := merge_left (literal (valuationOf q) (383)) (literal (valuationOf q) (391)) (countLit q [196, 197, 198]) (countLit q [199, 200, 201, 202]) (count391 q) 1 (meaning383 q) (meaning391 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 391 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (393)) (countLit q [190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202]) (count393 q) 1 (meaning379 q) (meaning393 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 393 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202])
  have hm := merge_left (literal (valuationOf q) (369)) (literal (valuationOf q) (395)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (count395 q) 1 (meaning369 q) (meaning395 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 395 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (397)) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (count397 q) 1 (meaning347 q) (meaning397 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 397 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 395 = false ∨ valuationOf q 398 = true := by
  have hs : count397 q = (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202])
  have hm := merge_two (literal (valuationOf q) (347)) (literal (valuationOf q) (395)) (literal (valuationOf q) (398)) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (count397 q) 1 1 (meaning347 q) (meaning395 q) (meaning398 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 395 = false ∨ valuationOf q 398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 395 = false ∨ valuation q 398 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 398 = true := by
  have hs : count397 q = (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202])
  have hm := merge_left (literal (valuationOf q) (348)) (literal (valuationOf q) (398)) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (count397 q) 2 (meaning348 q) (meaning398 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 398 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 398 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202])
  have hm := merge_right (literal (valuationOf q) (398)) (literal (valuationOf q) (400)) (countLit q [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (count399 q) 2 (meaning398 q) (meaning400 q) hs
  change valuationOf q 398 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 398 = false ∨ valuation q 400 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 397 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202])
  have hm := merge_two (literal (valuationOf q) (299)) (literal (valuationOf q) (397)) (literal (valuationOf q) (400)) (countLit q [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (count399 q) 1 1 (meaning299 q) (meaning397 q) (meaning400 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 397 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 397 = false ∨ valuation q 400 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 300 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202])
  have hm := merge_left (literal (valuationOf q) (300)) (literal (valuationOf q) (400)) (countLit q [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]) (count399 q) 2 (meaning300 q) (meaning400 q) hs
  change valuationOf q 300 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 300 = false ∨ valuation q 400 = true := counterClause253 (baseVal q)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 400 = false := by
  rw [value400]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count399 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause255 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1180 = true := by
  have hs : count1180 q = (countLit q [-5]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (1180)) (countLit q [-5]) (countLit q [-6]) (count1180 q) 1 (meaningNeg6 q) (meaning1180 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1180 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1180 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 1180 = false ∨ valuationOf q 1182 = true := by
  have hs : count1182 q = (countLit q [-2]) + (countLit q [-5, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -6])
  have hm := merge_right (literal (valuationOf q) (1180)) (literal (valuationOf q) (1182)) (countLit q [-2]) (countLit q [-5, -6]) (count1182 q) 1 (meaning1180 q) (meaning1182 q) hs
  change valuationOf q 1180 = false ∨ valuationOf q 1182 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 1180 = false ∨ valuation q 1182 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E154.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112154
