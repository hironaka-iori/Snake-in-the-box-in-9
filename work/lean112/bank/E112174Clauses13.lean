import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167, 168])
  have hm := merge_two (literal (valuationOf q) (321)) (literal (valuationOf q) (327)) (literal (valuationOf q) (330)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167, 168]) (count329 q) 1 1 (meaning321 q) (meaning327 q) (meaning330 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 327 = false ∨ valuation q 330 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 322 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167, 168])
  have hm := merge_left (literal (valuationOf q) (322)) (literal (valuationOf q) (330)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167, 168]) (count329 q) 2 (meaning322 q) (meaning330 q) hs
  change valuationOf q 322 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 322 = false ∨ valuation q 330 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168])
  have hm := merge_right (literal (valuationOf q) (329)) (literal (valuationOf q) (331)) (countLit q [156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168]) (count331 q) 1 (meaning329 q) (meaning331 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 331 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 330 = false ∨ valuationOf q 332 = true := by
  have hs : count331 q = (countLit q [156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168])
  have hm := merge_right (literal (valuationOf q) (330)) (literal (valuationOf q) (332)) (countLit q [156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168]) (count331 q) 2 (meaning330 q) (meaning332 q) hs
  change valuationOf q 330 = false ∨ valuationOf q 332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 330 = false ∨ valuation q 332 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168])
  have hm := merge_left (literal (valuationOf q) (317)) (literal (valuationOf q) (331)) (countLit q [156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168]) (count331 q) 1 (meaning317 q) (meaning331 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 331 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 329 = false ∨ valuationOf q 332 = true := by
  have hs : count331 q = (countLit q [156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168])
  have hm := merge_two (literal (valuationOf q) (317)) (literal (valuationOf q) (329)) (literal (valuationOf q) (332)) (countLit q [156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168]) (count331 q) 1 1 (meaning317 q) (meaning329 q) (meaning332 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 329 = false ∨ valuationOf q 332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 329 = false ∨ valuation q 332 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 318 = false ∨ valuationOf q 332 = true := by
  have hs : count331 q = (countLit q [156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168])
  have hm := merge_left (literal (valuationOf q) (318)) (literal (valuationOf q) (332)) (countLit q [156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168]) (count331 q) 2 (meaning318 q) (meaning332 q) hs
  change valuationOf q 318 = false ∨ valuationOf q 332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 318 = false ∨ valuation q 332 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_right (literal (valuationOf q) (171)) (literal (valuationOf q) (333)) (countLit q [170]) (countLit q [171]) (count333 q) 1 (meaning171 q) (meaning333 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 333 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_left (literal (valuationOf q) (170)) (literal (valuationOf q) (333)) (countLit q [170]) (countLit q [171]) (count333 q) 1 (meaning170 q) (meaning333 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 333 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 171 = false ∨ valuationOf q 334 = true := by
  have hs : count333 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_two (literal (valuationOf q) (170)) (literal (valuationOf q) (171)) (literal (valuationOf q) (334)) (countLit q [170]) (countLit q [171]) (count333 q) 1 1 (meaning170 q) (meaning171 q) (meaning334 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 171 = false ∨ valuationOf q 334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 171 = false ∨ valuation q 334 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [169]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170, 171])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [169]) (countLit q [170, 171]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 334 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [169]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170, 171])
  have hm := merge_right (literal (valuationOf q) (334)) (literal (valuationOf q) (336)) (countLit q [169]) (countLit q [170, 171]) (count335 q) 2 (meaning334 q) (meaning336 q) hs
  change valuationOf q 334 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 334 = false ∨ valuation q 336 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [173]) + (countLit q [175]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [175])
  have hm := merge_left (literal (valuationOf q) (173)) (literal (valuationOf q) (337)) (countLit q [173]) (countLit q [175]) (count337 q) 1 (meaning173 q) (meaning337 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 337 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [172]) + (countLit q [173, 175]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173, 175])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [172]) (countLit q [173, 175]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [169, 170, 171]) + (countLit q [172, 173, 175]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171]) (l₂ := [172, 173, 175])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [169, 170, 171]) (countLit q [172, 173, 175]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [169, 170, 171]) + (countLit q [172, 173, 175]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171]) (l₂ := [172, 173, 175])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (341)) (countLit q [169, 170, 171]) (countLit q [172, 173, 175]) (count341 q) 1 (meaning335 q) (meaning341 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 341 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [169, 170, 171]) + (countLit q [172, 173, 175]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171]) (l₂ := [172, 173, 175])
  have hm := merge_two (literal (valuationOf q) (335)) (literal (valuationOf q) (339)) (literal (valuationOf q) (342)) (countLit q [169, 170, 171]) (countLit q [172, 173, 175]) (count341 q) 1 1 (meaning335 q) (meaning339 q) (meaning342 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 339 = false ∨ valuation q 342 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 336 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [169, 170, 171]) + (countLit q [172, 173, 175]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171]) (l₂ := [172, 173, 175])
  have hm := merge_left (literal (valuationOf q) (336)) (literal (valuationOf q) (342)) (countLit q [169, 170, 171]) (countLit q [172, 173, 175]) (count341 q) 2 (meaning336 q) (meaning342 q) hs
  change valuationOf q 336 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 336 = false ∨ valuation q 342 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_right (literal (valuationOf q) (178)) (literal (valuationOf q) (343)) (countLit q [177]) (countLit q [178]) (count343 q) 1 (meaning178 q) (meaning343 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 343 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 177 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_left (literal (valuationOf q) (177)) (literal (valuationOf q) (343)) (countLit q [177]) (countLit q [178]) (count343 q) 1 (meaning177 q) (meaning343 q) hs
  change valuationOf q 177 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 343 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177, 178])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [176]) (countLit q [177, 178]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 179 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [179]) + (countLit q [180]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180])
  have hm := merge_left (literal (valuationOf q) (179)) (literal (valuationOf q) (347)) (countLit q [179]) (countLit q [180]) (count347 q) 1 (meaning179 q) (meaning347 q) hs
  change valuationOf q 179 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 347 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [181]) + (countLit q [182]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182])
  have hm := merge_left (literal (valuationOf q) (181)) (literal (valuationOf q) (349)) (countLit q [181]) (countLit q [182]) (count349 q) 1 (meaning181 q) (meaning349 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 349 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [179, 180]) + (countLit q [181, 182]) := List.countP_append (p := literal q) (l₁ := [179, 180]) (l₂ := [181, 182])
  have hm := merge_right (literal (valuationOf q) (349)) (literal (valuationOf q) (351)) (countLit q [179, 180]) (countLit q [181, 182]) (count351 q) 1 (meaning349 q) (meaning351 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 351 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [179, 180]) + (countLit q [181, 182]) := List.countP_append (p := literal q) (l₁ := [179, 180]) (l₂ := [181, 182])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (351)) (countLit q [179, 180]) (countLit q [181, 182]) (count351 q) 1 (meaning347 q) (meaning351 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 351 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [176, 177, 178]) (countLit q [179, 180, 181, 182]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (345)) (literal (valuationOf q) (353)) (countLit q [176, 177, 178]) (countLit q [179, 180, 181, 182]) (count353 q) 1 (meaning345 q) (meaning353 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 353 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [169, 170, 171, 172, 173, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172, 173, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [169, 170, 171, 172, 173, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [169, 170, 171, 172, 173, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172, 173, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (355)) (countLit q [169, 170, 171, 172, 173, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182]) (count355 q) 1 (meaning341 q) (meaning355 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 355 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 353 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [169, 170, 171, 172, 173, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172, 173, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182])
  have hm := merge_two (literal (valuationOf q) (341)) (literal (valuationOf q) (353)) (literal (valuationOf q) (356)) (countLit q [169, 170, 171, 172, 173, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182]) (count355 q) 1 1 (meaning341 q) (meaning353 q) (meaning356 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 353 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 353 = false ∨ valuation q 356 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 342 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [169, 170, 171, 172, 173, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172, 173, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (342)) (literal (valuationOf q) (356)) (countLit q [169, 170, 171, 172, 173, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182]) (count355 q) 2 (meaning342 q) (meaning356 q) hs
  change valuationOf q 342 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 342 = false ∨ valuation q 356 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (355)) (literal (valuationOf q) (357)) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 1 (meaning355 q) (meaning357 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 357 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E174.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112174
