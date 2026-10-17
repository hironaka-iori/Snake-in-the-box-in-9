import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168, 169])
  have hm := merge_left (literal (valuationOf q) (167)) (literal (valuationOf q) (331)) (countLit q [167]) (countLit q [168, 169]) (count331 q) 1 (meaning167 q) (meaning331 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 331 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 329 = false ∨ valuationOf q 332 = true := by
  have hs : count331 q = (countLit q [167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168, 169])
  have hm := merge_two (literal (valuationOf q) (167)) (literal (valuationOf q) (329)) (literal (valuationOf q) (332)) (countLit q [167]) (countLit q [168, 169]) (count331 q) 1 1 (meaning167 q) (meaning329 q) (meaning332 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 329 = false ∨ valuationOf q 332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 329 = false ∨ valuation q 332 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [172]) + (countLit q [173]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173])
  have hm := merge_right (literal (valuationOf q) (173)) (literal (valuationOf q) (335)) (countLit q [172]) (countLit q [173]) (count335 q) 1 (meaning173 q) (meaning335 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 335 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 172 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [172]) + (countLit q [173]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173])
  have hm := merge_left (literal (valuationOf q) (172)) (literal (valuationOf q) (335)) (countLit q [172]) (countLit q [173]) (count335 q) 1 (meaning172 q) (meaning335 q) hs
  change valuationOf q 172 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 335 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 172 = false ∨ valuationOf q 173 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [172]) + (countLit q [173]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173])
  have hm := merge_two (literal (valuationOf q) (172)) (literal (valuationOf q) (173)) (literal (valuationOf q) (336)) (countLit q [172]) (countLit q [173]) (count335 q) 1 1 (meaning172 q) (meaning173 q) (meaning336 q) hs
  change valuationOf q 172 = false ∨ valuationOf q 173 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 173 = false ∨ valuation q 336 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [170, 171]) + (countLit q [172, 173]) := List.countP_append (p := literal q) (l₁ := [170, 171]) (l₂ := [172, 173])
  have hm := merge_right (literal (valuationOf q) (335)) (literal (valuationOf q) (337)) (countLit q [170, 171]) (countLit q [172, 173]) (count337 q) 1 (meaning335 q) (meaning337 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 337 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 336 = false ∨ valuationOf q 338 = true := by
  have hs : count337 q = (countLit q [170, 171]) + (countLit q [172, 173]) := List.countP_append (p := literal q) (l₁ := [170, 171]) (l₂ := [172, 173])
  have hm := merge_right (literal (valuationOf q) (336)) (literal (valuationOf q) (338)) (countLit q [170, 171]) (countLit q [172, 173]) (count337 q) 2 (meaning336 q) (meaning338 q) hs
  change valuationOf q 336 = false ∨ valuationOf q 338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 336 = false ∨ valuation q 338 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [167, 168, 169]) + (countLit q [170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169]) (l₂ := [170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [167, 168, 169]) (countLit q [170, 171, 172, 173]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 338 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [167, 168, 169]) + (countLit q [170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169]) (l₂ := [170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (338)) (literal (valuationOf q) (340)) (countLit q [167, 168, 169]) (countLit q [170, 171, 172, 173]) (count339 q) 2 (meaning338 q) (meaning340 q) hs
  change valuationOf q 338 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 338 = false ∨ valuation q 340 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [167, 168, 169]) + (countLit q [170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169]) (l₂ := [170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (331)) (literal (valuationOf q) (339)) (countLit q [167, 168, 169]) (countLit q [170, 171, 172, 173]) (count339 q) 1 (meaning331 q) (meaning339 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 339 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [167, 168, 169]) + (countLit q [170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169]) (l₂ := [170, 171, 172, 173])
  have hm := merge_two (literal (valuationOf q) (331)) (literal (valuationOf q) (337)) (literal (valuationOf q) (340)) (countLit q [167, 168, 169]) (countLit q [170, 171, 172, 173]) (count339 q) 1 1 (meaning331 q) (meaning337 q) (meaning340 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 337 = false ∨ valuation q 340 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 332 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [167, 168, 169]) + (countLit q [170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169]) (l₂ := [170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (332)) (literal (valuationOf q) (340)) (countLit q [167, 168, 169]) (countLit q [170, 171, 172, 173]) (count339 q) 2 (meaning332 q) (meaning340 q) hs
  change valuationOf q 332 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 332 = false ∨ valuation q 340 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [174]) + (countLit q [175]) := List.countP_append (p := literal q) (l₁ := [174]) (l₂ := [175])
  have hm := merge_right (literal (valuationOf q) (175)) (literal (valuationOf q) (341)) (countLit q [174]) (countLit q [175]) (count341 q) 1 (meaning175 q) (meaning341 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 341 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 176 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [176]) + (countLit q [177]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177])
  have hm := merge_left (literal (valuationOf q) (176)) (literal (valuationOf q) (343)) (countLit q [176]) (countLit q [177]) (count343 q) 1 (meaning176 q) (meaning343 q) hs
  change valuationOf q 176 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 343 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [174, 175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [174, 175]) (l₂ := [176, 177])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [174, 175]) (countLit q [176, 177]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [174, 175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [174, 175]) (l₂ := [176, 177])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (345)) (countLit q [174, 175]) (countLit q [176, 177]) (count345 q) 1 (meaning341 q) (meaning345 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 345 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [174, 175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [174, 175]) (l₂ := [176, 177])
  have hm := merge_two (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (literal (valuationOf q) (346)) (countLit q [174, 175]) (countLit q [176, 177]) (count345 q) 1 1 (meaning341 q) (meaning343 q) (meaning346 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = false ∨ valuation q 346 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 179 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [178]) + (countLit q [179]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [179])
  have hm := merge_right (literal (valuationOf q) (179)) (literal (valuationOf q) (347)) (countLit q [178]) (countLit q [179]) (count347 q) 1 (meaning179 q) (meaning347 q) hs
  change valuationOf q 179 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 347 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 182 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [180]) + (countLit q [182]) := List.countP_append (p := literal q) (l₁ := [180]) (l₂ := [182])
  have hm := merge_right (literal (valuationOf q) (182)) (literal (valuationOf q) (349)) (countLit q [180]) (countLit q [182]) (count349 q) 1 (meaning182 q) (meaning349 q) hs
  change valuationOf q 182 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 349 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [178, 179]) + (countLit q [180, 182]) := List.countP_append (p := literal q) (l₁ := [178, 179]) (l₂ := [180, 182])
  have hm := merge_right (literal (valuationOf q) (349)) (literal (valuationOf q) (351)) (countLit q [178, 179]) (countLit q [180, 182]) (count351 q) 1 (meaning349 q) (meaning351 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 351 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [178, 179]) + (countLit q [180, 182]) := List.countP_append (p := literal q) (l₁ := [178, 179]) (l₂ := [180, 182])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (351)) (countLit q [178, 179]) (countLit q [180, 182]) (count351 q) 1 (meaning347 q) (meaning351 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 351 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 349 = false ∨ valuationOf q 352 = true := by
  have hs : count351 q = (countLit q [178, 179]) + (countLit q [180, 182]) := List.countP_append (p := literal q) (l₁ := [178, 179]) (l₂ := [180, 182])
  have hm := merge_two (literal (valuationOf q) (347)) (literal (valuationOf q) (349)) (literal (valuationOf q) (352)) (countLit q [178, 179]) (countLit q [180, 182]) (count351 q) 1 1 (meaning347 q) (meaning349 q) (meaning352 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 349 = false ∨ valuationOf q 352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 349 = false ∨ valuation q 352 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [174, 175, 176, 177]) + (countLit q [178, 179, 180, 182]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177]) (l₂ := [178, 179, 180, 182])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [174, 175, 176, 177]) (countLit q [178, 179, 180, 182]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 352 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [174, 175, 176, 177]) + (countLit q [178, 179, 180, 182]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177]) (l₂ := [178, 179, 180, 182])
  have hm := merge_right (literal (valuationOf q) (352)) (literal (valuationOf q) (354)) (countLit q [174, 175, 176, 177]) (countLit q [178, 179, 180, 182]) (count353 q) 2 (meaning352 q) (meaning354 q) hs
  change valuationOf q 352 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 352 = false ∨ valuation q 354 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [174, 175, 176, 177]) + (countLit q [178, 179, 180, 182]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177]) (l₂ := [178, 179, 180, 182])
  have hm := merge_left (literal (valuationOf q) (345)) (literal (valuationOf q) (353)) (countLit q [174, 175, 176, 177]) (countLit q [178, 179, 180, 182]) (count353 q) 1 (meaning345 q) (meaning353 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 353 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [174, 175, 176, 177]) + (countLit q [178, 179, 180, 182]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177]) (l₂ := [178, 179, 180, 182])
  have hm := merge_two (literal (valuationOf q) (345)) (literal (valuationOf q) (351)) (literal (valuationOf q) (354)) (countLit q [174, 175, 176, 177]) (countLit q [178, 179, 180, 182]) (count353 q) 1 1 (meaning345 q) (meaning351 q) (meaning354 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 351 = false ∨ valuation q 354 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 346 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [174, 175, 176, 177]) + (countLit q [178, 179, 180, 182]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177]) (l₂ := [178, 179, 180, 182])
  have hm := merge_left (literal (valuationOf q) (346)) (literal (valuationOf q) (354)) (countLit q [174, 175, 176, 177]) (countLit q [178, 179, 180, 182]) (count353 q) 2 (meaning346 q) (meaning354 q) hs
  change valuationOf q 346 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 346 = false ∨ valuation q 354 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [167, 168, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180, 182]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180, 182])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [167, 168, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180, 182]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 354 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [167, 168, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180, 182]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180, 182])
  have hm := merge_right (literal (valuationOf q) (354)) (literal (valuationOf q) (356)) (countLit q [167, 168, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180, 182]) (count355 q) 2 (meaning354 q) (meaning356 q) hs
  change valuationOf q 354 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 354 = false ∨ valuation q 356 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [167, 168, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180, 182]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180, 182])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (355)) (countLit q [167, 168, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180, 182]) (count355 q) 1 (meaning339 q) (meaning355 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 355 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 353 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [167, 168, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180, 182]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180, 182])
  have hm := merge_two (literal (valuationOf q) (339)) (literal (valuationOf q) (353)) (literal (valuationOf q) (356)) (countLit q [167, 168, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180, 182]) (count355 q) 1 1 (meaning339 q) (meaning353 q) (meaning356 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 353 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 353 = false ∨ valuation q 356 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 340 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [167, 168, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180, 182]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180, 182])
  have hm := merge_left (literal (valuationOf q) (340)) (literal (valuationOf q) (356)) (countLit q [167, 168, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180, 182]) (count355 q) 2 (meaning340 q) (meaning356 q) hs
  change valuationOf q 340 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 340 = false ∨ valuation q 356 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E019.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112019
