import E112170Semantics
import B112E170Inputs
namespace Snake9.Regrowth.E112170
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (371)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191]) (count371 q) 1 (meaning365 q) (meaning371 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 371 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [195]) + (countLit q [196]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196])
  have hm := merge_right (literal (valuationOf q) (196)) (literal (valuationOf q) (377)) (countLit q [195]) (countLit q [196]) (count377 q) 1 (meaning196 q) (meaning377 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 377 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 198 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_right (literal (valuationOf q) (198)) (literal (valuationOf q) (379)) (countLit q [197]) (countLit q [198]) (count379 q) 1 (meaning198 q) (meaning379 q) hs
  change valuationOf q 198 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 379 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [195, 196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [195, 196]) (l₂ := [197, 198])
  have hm := merge_right (literal (valuationOf q) (379)) (literal (valuationOf q) (381)) (countLit q [195, 196]) (countLit q [197, 198]) (count381 q) 1 (meaning379 q) (meaning381 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 381 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [195, 196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [195, 196]) (l₂ := [197, 198])
  have hm := merge_left (literal (valuationOf q) (377)) (literal (valuationOf q) (381)) (countLit q [195, 196]) (countLit q [197, 198]) (count381 q) 1 (meaning377 q) (meaning381 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 381 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [192, 193, 194]) (countLit q [195, 196, 197, 198]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (371)) (literal (valuationOf q) (385)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count385 q) 1 (meaning371 q) (meaning385 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 385 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (361)) (literal (valuationOf q) (387)) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count387 q) 1 (meaning361 q) (meaning387 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 387 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count389 q) 1 (meaning387 q) (meaning389 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (389)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count389 q) 1 (meaning339 q) (meaning389 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 389 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_two (literal (valuationOf q) (293)) (literal (valuationOf q) (389)) (literal (valuationOf q) (392)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count391 q) 1 1 (meaning293 q) (meaning389 q) (meaning392 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 389 = false ∨ valuation q 392 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (294)) (literal (valuationOf q) (392)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count391 q) 2 (meaning294 q) (meaning392 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 392 = true := counterClause239 (baseVal q)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 392 = false := by
  rw [value392]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count391 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause241 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1149 = true := by
  have hs : count1149 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1149)) (countLit q [-3]) (countLit q [-5]) (count1149 q) 1 (meaningNeg5 q) (meaning1149 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1149 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1149 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1149 = true := by
  have hs : count1149 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1149)) (countLit q [-3]) (countLit q [-5]) (count1149 q) 1 (meaningNeg3 q) (meaning1149 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1149 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1149 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1150 = true := by
  have hs : count1149 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1150)) (countLit q [-3]) (countLit q [-5]) (count1149 q) 1 1 (meaningNeg3 q) (meaningNeg5 q) (meaning1150 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1150 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 5 = true ∨ valuation q 1150 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1151 = true := by
  have hs : count1151 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1151)) (countLit q [-2]) (countLit q [-3, -5]) (count1151 q) 1 (meaningNeg2 q) (meaning1151 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1151 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1151 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1149 = false ∨ valuationOf q 1152 = true := by
  have hs : count1151 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1149)) (literal (valuationOf q) (1152)) (countLit q [-2]) (countLit q [-3, -5]) (count1151 q) 1 1 (meaningNeg2 q) (meaning1149 q) (meaning1152 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1149 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1149 = false ∨ valuation q 1152 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1150 = false ∨ valuationOf q 1153 = true := by
  have hs : count1151 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1150)) (literal (valuationOf q) (1153)) (countLit q [-2]) (countLit q [-3, -5]) (count1151 q) 1 2 (meaningNeg2 q) (meaning1150 q) (meaning1153 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1150 = false ∨ valuationOf q 1153 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1150 = false ∨ valuation q 1153 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1154 = true := by
  have hs : count1154 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (1154)) (countLit q [-10]) (countLit q [-11]) (count1154 q) 1 (meaningNeg11 q) (meaning1154 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1154 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1154 = true := by
  have hs : count1154 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1154)) (countLit q [-10]) (countLit q [-11]) (count1154 q) 1 (meaningNeg10 q) (meaning1154 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1154 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 11 = true ∨ valuationOf q 1155 = true := by
  have hs : count1154 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (-11)) (literal (valuationOf q) (1155)) (countLit q [-10]) (countLit q [-11]) (count1154 q) 1 1 (meaningNeg10 q) (meaningNeg11 q) (meaning1155 q) hs
  change (! (valuationOf q 10)) = false ∨ (! (valuationOf q 11)) = false ∨ valuationOf q 1155 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 11 = true ∨ valuation q 1155 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 1154 = false ∨ valuationOf q 1156 = true := by
  have hs : count1156 q = (countLit q [-8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -11])
  have hm := merge_right (literal (valuationOf q) (1154)) (literal (valuationOf q) (1156)) (countLit q [-8]) (countLit q [-10, -11]) (count1156 q) 1 (meaning1154 q) (meaning1156 q) hs
  change valuationOf q 1154 = false ∨ valuationOf q 1156 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 1154 = false ∨ valuation q 1156 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1156 = true := by
  have hs : count1156 q = (countLit q [-8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -11])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1156)) (countLit q [-8]) (countLit q [-10, -11]) (count1156 q) 1 (meaningNeg8 q) (meaning1156 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1156 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1156 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1154 = false ∨ valuationOf q 1157 = true := by
  have hs : count1156 q = (countLit q [-8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -11])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1154)) (literal (valuationOf q) (1157)) (countLit q [-8]) (countLit q [-10, -11]) (count1156 q) 1 1 (meaningNeg8 q) (meaning1154 q) (meaning1157 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1154 = false ∨ valuationOf q 1157 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1154 = false ∨ valuation q 1157 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1155 = false ∨ valuationOf q 1158 = true := by
  have hs : count1156 q = (countLit q [-8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -11])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1155)) (literal (valuationOf q) (1158)) (countLit q [-8]) (countLit q [-10, -11]) (count1156 q) 1 2 (meaningNeg8 q) (meaning1155 q) (meaning1158 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1155 = false ∨ valuationOf q 1158 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1155 = false ∨ valuation q 1158 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 1158 = false ∨ valuationOf q 1161 = true := by
  have hs : count1159 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11])
  have hm := merge_right (literal (valuationOf q) (1158)) (literal (valuationOf q) (1161)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11]) (count1159 q) 3 (meaning1158 q) (meaning1161 q) hs
  change valuationOf q 1158 = false ∨ valuationOf q 1161 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 1158 = false ∨ valuation q 1161 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 1151 = false ∨ valuationOf q 1159 = true := by
  have hs : count1159 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11])
  have hm := merge_left (literal (valuationOf q) (1151)) (literal (valuationOf q) (1159)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11]) (count1159 q) 1 (meaning1151 q) (meaning1159 q) hs
  change valuationOf q 1151 = false ∨ valuationOf q 1159 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 1151 = false ∨ valuation q 1159 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 1151 = false ∨ valuationOf q 1156 = false ∨ valuationOf q 1160 = true := by
  have hs : count1159 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1151)) (literal (valuationOf q) (1156)) (literal (valuationOf q) (1160)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11]) (count1159 q) 1 1 (meaning1151 q) (meaning1156 q) (meaning1160 q) hs
  change valuationOf q 1151 = false ∨ valuationOf q 1156 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 1151 = false ∨ valuation q 1156 = false ∨ valuation q 1160 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E170.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112170
