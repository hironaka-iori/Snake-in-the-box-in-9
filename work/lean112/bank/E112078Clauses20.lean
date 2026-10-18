import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [156, 157]) + (countLit q [158, 159]) := List.countP_append (p := literal q) (l₁ := [156, 157]) (l₂ := [158, 159])
  have hm := merge_left (literal (valuationOf q) (307)) (literal (valuationOf q) (311)) (countLit q [156, 157]) (countLit q [158, 159]) (count311 q) 1 (meaning307 q) (meaning311 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 311 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [160]) + (countLit q [161]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161])
  have hm := merge_left (literal (valuationOf q) (160)) (literal (valuationOf q) (313)) (countLit q [160]) (countLit q [161]) (count313 q) 1 (meaning160 q) (meaning313 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 313 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [160, 161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [160, 161]) (l₂ := [162, 163])
  have hm := merge_left (literal (valuationOf q) (313)) (literal (valuationOf q) (317)) (countLit q [160, 161]) (countLit q [162, 163]) (count317 q) 1 (meaning313 q) (meaning317 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 317 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [156, 157, 158, 159]) + (countLit q [160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159]) (l₂ := [160, 161, 162, 163])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [156, 157, 158, 159]) (countLit q [160, 161, 162, 163]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [156, 157, 158, 159]) + (countLit q [160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159]) (l₂ := [160, 161, 162, 163])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (319)) (countLit q [156, 157, 158, 159]) (countLit q [160, 161, 162, 163]) (count319 q) 1 (meaning311 q) (meaning319 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 319 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163])
  have hm := merge_right (literal (valuationOf q) (319)) (literal (valuationOf q) (321)) (countLit q [149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163]) (count321 q) 1 (meaning319 q) (meaning321 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 321 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163])
  have hm := merge_left (literal (valuationOf q) (305)) (literal (valuationOf q) (321)) (countLit q [149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163]) (count321 q) 1 (meaning305 q) (meaning321 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 321 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165, 166])
  have hm := merge_left (literal (valuationOf q) (164)) (literal (valuationOf q) (325)) (countLit q [164]) (countLit q [165, 166]) (count325 q) 1 (meaning164 q) (meaning325 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 325 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_left (literal (valuationOf q) (167)) (literal (valuationOf q) (327)) (countLit q [167]) (countLit q [168]) (count327 q) 1 (meaning167 q) (meaning327 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 327 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_right (literal (valuationOf q) (170)) (literal (valuationOf q) (329)) (countLit q [169]) (countLit q [170]) (count329 q) 1 (meaning170 q) (meaning329 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 329 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_left (literal (valuationOf q) (169)) (literal (valuationOf q) (329)) (countLit q [169]) (countLit q [170]) (count329 q) 1 (meaning169 q) (meaning329 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 329 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_right (literal (valuationOf q) (329)) (literal (valuationOf q) (331)) (countLit q [167, 168]) (countLit q [169, 170]) (count331 q) 1 (meaning329 q) (meaning331 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 331 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_left (literal (valuationOf q) (327)) (literal (valuationOf q) (331)) (countLit q [167, 168]) (countLit q [169, 170]) (count331 q) 1 (meaning327 q) (meaning331 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 331 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [164, 165, 166]) + (countLit q [167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166]) (l₂ := [167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [164, 165, 166]) (countLit q [167, 168, 169, 170]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [164, 165, 166]) + (countLit q [167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166]) (l₂ := [167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (325)) (literal (valuationOf q) (333)) (countLit q [164, 165, 166]) (countLit q [167, 168, 169, 170]) (count333 q) 1 (meaning325 q) (meaning333 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 333 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_right (literal (valuationOf q) (178)) (literal (valuationOf q) (343)) (countLit q [177]) (countLit q [178]) (count343 q) 1 (meaning178 q) (meaning343 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 343 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 177 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_left (literal (valuationOf q) (177)) (literal (valuationOf q) (343)) (countLit q [177]) (countLit q [178]) (count343 q) 1 (meaning177 q) (meaning343 q) hs
  change valuationOf q 177 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 343 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [175, 176]) (countLit q [177, 178]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [171, 172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [171, 172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (347)) (literal (valuationOf q) (349)) (countLit q [164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) (count349 q) 1 (meaning347 q) (meaning349 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 349 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (333)) (literal (valuationOf q) (349)) (countLit q [164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) (count349 q) 1 (meaning333 q) (meaning349 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 349 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (349)) (literal (valuationOf q) (351)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count351 q) 1 (meaning349 q) (meaning351 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 351 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (321)) (literal (valuationOf q) (351)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count351 q) 1 (meaning321 q) (meaning351 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 351 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (293)) (literal (valuationOf q) (353)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count353 q) 1 (meaning293 q) (meaning353 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 353 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_two (literal (valuationOf q) (293)) (literal (valuationOf q) (351)) (literal (valuationOf q) (354)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count353 q) 1 1 (meaning293 q) (meaning351 q) (meaning354 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 351 = false ∨ valuation q 354 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (294)) (literal (valuationOf q) (354)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count353 q) 2 (meaning294 q) (meaning354 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 354 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [182]) + (countLit q [183]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183])
  have hm := merge_right (literal (valuationOf q) (183)) (literal (valuationOf q) (359)) (countLit q [182]) (countLit q [183]) (count359 q) 1 (meaning183 q) (meaning359 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 359 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 184 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [184]) + (countLit q [185]) := List.countP_append (p := literal q) (l₁ := [184]) (l₂ := [185])
  have hm := merge_left (literal (valuationOf q) (184)) (literal (valuationOf q) (361)) (countLit q [184]) (countLit q [185]) (count361 q) 1 (meaning184 q) (meaning361 q) hs
  change valuationOf q 184 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 361 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [182, 183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [182, 183]) (l₂ := [184, 185])
  have hm := merge_right (literal (valuationOf q) (361)) (literal (valuationOf q) (363)) (countLit q [182, 183]) (countLit q [184, 185]) (count363 q) 1 (meaning361 q) (meaning363 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 363 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 361 = false ∨ valuationOf q 364 = true := by
  have hs : count363 q = (countLit q [182, 183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [182, 183]) (l₂ := [184, 185])
  have hm := merge_two (literal (valuationOf q) (359)) (literal (valuationOf q) (361)) (literal (valuationOf q) (364)) (countLit q [182, 183]) (countLit q [184, 185]) (count363 q) 1 1 (meaning359 q) (meaning361 q) (meaning364 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 361 = false ∨ valuationOf q 364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = false ∨ valuation q 364 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [179, 180, 181]) + (countLit q [182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181]) (l₂ := [182, 183, 184, 185])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [179, 180, 181]) (countLit q [182, 183, 184, 185]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E078.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112078
