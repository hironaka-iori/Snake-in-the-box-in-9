import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (339)) (countLit q [158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172]) (count339 q) 1 (meaning323 q) (meaning339 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 339 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172])
  have hm := merge_two (literal (valuationOf q) (323)) (literal (valuationOf q) (337)) (literal (valuationOf q) (340)) (countLit q [158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172]) (count339 q) 1 1 (meaning323 q) (meaning337 q) (meaning340 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 337 = false ∨ valuation q 340 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 174 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174])
  have hm := merge_right (literal (valuationOf q) (174)) (literal (valuationOf q) (341)) (countLit q [173]) (countLit q [174]) (count341 q) 1 (meaning174 q) (meaning341 q) hs
  change valuationOf q 174 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 341 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176])
  have hm := merge_left (literal (valuationOf q) (175)) (literal (valuationOf q) (343)) (countLit q [175]) (countLit q [176]) (count343 q) 1 (meaning175 q) (meaning343 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 343 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [173, 174]) + (countLit q [175, 176]) := List.countP_append (p := literal q) (l₁ := [173, 174]) (l₂ := [175, 176])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [173, 174]) (countLit q [175, 176]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [173, 174]) + (countLit q [175, 176]) := List.countP_append (p := literal q) (l₁ := [173, 174]) (l₂ := [175, 176])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (345)) (countLit q [173, 174]) (countLit q [175, 176]) (count345 q) 1 (meaning341 q) (meaning345 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 345 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_right (literal (valuationOf q) (178)) (literal (valuationOf q) (347)) (countLit q [177]) (countLit q [178]) (count347 q) 1 (meaning178 q) (meaning347 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 347 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [177, 178]) + (countLit q [179, 180]) := List.countP_append (p := literal q) (l₁ := [177, 178]) (l₂ := [179, 180])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (351)) (countLit q [177, 178]) (countLit q [179, 180]) (count351 q) 1 (meaning347 q) (meaning351 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 351 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [173, 174, 175, 176]) + (countLit q [177, 178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [173, 174, 175, 176]) (l₂ := [177, 178, 179, 180])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [173, 174, 175, 176]) (countLit q [177, 178, 179, 180]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [173, 174, 175, 176]) + (countLit q [177, 178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [173, 174, 175, 176]) (l₂ := [177, 178, 179, 180])
  have hm := merge_left (literal (valuationOf q) (345)) (literal (valuationOf q) (353)) (countLit q [173, 174, 175, 176]) (countLit q [177, 178, 179, 180]) (count353 q) 1 (meaning345 q) (meaning353 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 353 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 182 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [181]) + (countLit q [182]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182])
  have hm := merge_right (literal (valuationOf q) (182)) (literal (valuationOf q) (355)) (countLit q [181]) (countLit q [182]) (count355 q) 1 (meaning182 q) (meaning355 q) hs
  change valuationOf q 182 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 355 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [181]) + (countLit q [182]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182])
  have hm := merge_left (literal (valuationOf q) (181)) (literal (valuationOf q) (355)) (countLit q [181]) (countLit q [182]) (count355 q) 1 (meaning181 q) (meaning355 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 355 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 182 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [181]) + (countLit q [182]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182])
  have hm := merge_two (literal (valuationOf q) (181)) (literal (valuationOf q) (182)) (literal (valuationOf q) (356)) (countLit q [181]) (countLit q [182]) (count355 q) 1 1 (meaning181 q) (meaning182 q) (meaning356 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 182 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 182 = false ∨ valuation q 356 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 184 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [183]) + (countLit q [184]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184])
  have hm := merge_right (literal (valuationOf q) (184)) (literal (valuationOf q) (357)) (countLit q [183]) (countLit q [184]) (count357 q) 1 (meaning184 q) (meaning357 q) hs
  change valuationOf q 184 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 357 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [181, 182]) + (countLit q [183, 184]) := List.countP_append (p := literal q) (l₁ := [181, 182]) (l₂ := [183, 184])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [181, 182]) (countLit q [183, 184]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [181, 182]) + (countLit q [183, 184]) := List.countP_append (p := literal q) (l₁ := [181, 182]) (l₂ := [183, 184])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (359)) (countLit q [181, 182]) (countLit q [183, 184]) (count359 q) 1 (meaning355 q) (meaning359 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 359 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 356 = false ∨ valuationOf q 360 = true := by
  have hs : count359 q = (countLit q [181, 182]) + (countLit q [183, 184]) := List.countP_append (p := literal q) (l₁ := [181, 182]) (l₂ := [183, 184])
  have hm := merge_left (literal (valuationOf q) (356)) (literal (valuationOf q) (360)) (countLit q [181, 182]) (countLit q [183, 184]) (count359 q) 2 (meaning356 q) (meaning360 q) hs
  change valuationOf q 356 = false ∨ valuationOf q 360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 356 = false ∨ valuation q 360 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [181, 182, 183, 184]) + (countLit q [185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [181, 182, 183, 184]) (l₂ := [185, 186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (367)) (countLit q [181, 182, 183, 184]) (countLit q [185, 186, 187, 188]) (count367 q) 1 (meaning359 q) (meaning367 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 367 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 360 = false ∨ valuationOf q 368 = true := by
  have hs : count367 q = (countLit q [181, 182, 183, 184]) + (countLit q [185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [181, 182, 183, 184]) (l₂ := [185, 186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (360)) (literal (valuationOf q) (368)) (countLit q [181, 182, 183, 184]) (countLit q [185, 186, 187, 188]) (count367 q) 2 (meaning360 q) (meaning368 q) hs
  change valuationOf q 360 = false ∨ valuationOf q 368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 360 = false ∨ valuation q 368 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [173, 174, 175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [173, 174, 175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (367)) (literal (valuationOf q) (369)) (countLit q [173, 174, 175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187, 188]) (count369 q) 1 (meaning367 q) (meaning369 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 369 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 368 = false ∨ valuationOf q 370 = true := by
  have hs : count369 q = (countLit q [173, 174, 175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [173, 174, 175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (368)) (literal (valuationOf q) (370)) (countLit q [173, 174, 175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187, 188]) (count369 q) 2 (meaning368 q) (meaning370 q) hs
  change valuationOf q 368 = false ∨ valuationOf q 370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 368 = false ∨ valuation q 370 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [173, 174, 175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [173, 174, 175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (353)) (literal (valuationOf q) (369)) (countLit q [173, 174, 175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187, 188]) (count369 q) 1 (meaning353 q) (meaning369 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 369 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 367 = false ∨ valuationOf q 370 = true := by
  have hs : count369 q = (countLit q [173, 174, 175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [173, 174, 175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187, 188])
  have hm := merge_two (literal (valuationOf q) (353)) (literal (valuationOf q) (367)) (literal (valuationOf q) (370)) (countLit q [173, 174, 175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187, 188]) (count369 q) 1 1 (meaning353 q) (meaning367 q) (meaning370 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 367 = false ∨ valuationOf q 370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 367 = false ∨ valuation q 370 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) + (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (l₂ := [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 370 = false ∨ valuationOf q 372 = true := by
  have hs : count371 q = (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) + (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (l₂ := [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (370)) (literal (valuationOf q) (372)) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (count371 q) 2 (meaning370 q) (meaning372 q) hs
  change valuationOf q 370 = false ∨ valuationOf q 372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 370 = false ∨ valuation q 372 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) + (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (l₂ := [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (371)) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (count371 q) 1 (meaning339 q) (meaning371 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 371 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 369 = false ∨ valuationOf q 372 = true := by
  have hs : count371 q = (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) + (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (l₂ := [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188])
  have hm := merge_two (literal (valuationOf q) (339)) (literal (valuationOf q) (369)) (literal (valuationOf q) (372)) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (count371 q) 1 1 (meaning339 q) (meaning369 q) (meaning372 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 369 = false ∨ valuationOf q 372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 369 = false ∨ valuation q 372 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 340 = false ∨ valuationOf q 372 = true := by
  have hs : count371 q = (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) + (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (l₂ := [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (340)) (literal (valuationOf q) (372)) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (count371 q) 2 (meaning340 q) (meaning372 q) hs
  change valuationOf q 340 = false ∨ valuationOf q 372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 340 = false ∨ valuation q 372 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) + (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (l₂ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 372 = false ∨ valuationOf q 374 = true := by
  have hs : count373 q = (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) + (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (l₂ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (372)) (literal (valuationOf q) (374)) (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (count373 q) 2 (meaning372 q) (meaning374 q) hs
  change valuationOf q 372 = false ∨ valuationOf q 374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 372 = false ∨ valuation q 374 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) + (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (l₂ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (373)) (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (count373 q) 1 (meaning311 q) (meaning373 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 373 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 371 = false ∨ valuationOf q 374 = true := by
  have hs : count373 q = (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) + (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (l₂ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188])
  have hm := merge_two (literal (valuationOf q) (311)) (literal (valuationOf q) (371)) (literal (valuationOf q) (374)) (countLit q [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (count373 q) 1 1 (meaning311 q) (meaning371 q) (meaning374 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 371 = false ∨ valuationOf q 374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 371 = false ∨ valuation q 374 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E121.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112121
