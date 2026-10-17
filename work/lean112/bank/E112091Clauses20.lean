import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1303 = true := by
  have hs : count1303 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1303)) (countLit q [-27]) (countLit q [-29, -30]) (count1303 q) 1 (meaningNeg27 q) (meaning1303 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1303 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1301 = false ∨ valuationOf q 1304 = true := by
  have hs : count1303 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (1301)) (literal (valuationOf q) (1304)) (countLit q [-27]) (countLit q [-29, -30]) (count1303 q) 1 1 (meaningNeg27 q) (meaning1301 q) (meaning1304 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1301 = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1301 = false ∨ valuation q 1304 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1302 = false ∨ valuationOf q 1305 = true := by
  have hs : count1303 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (1302)) (literal (valuationOf q) (1305)) (countLit q [-27]) (countLit q [-29, -30]) (count1303 q) 1 2 (meaningNeg27 q) (meaning1302 q) (meaning1305 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1302 = false ∨ valuationOf q 1305 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1302 = false ∨ valuation q 1305 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1306)) (countLit q [-35]) (countLit q [-37]) (count1306 q) 1 (meaningNeg37 q) (meaning1306 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1306 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1306)) (countLit q [-35]) (countLit q [-37]) (count1306 q) 1 (meaningNeg35 q) (meaning1306 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1306 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1307 = true := by
  have hs : count1306 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1307)) (countLit q [-35]) (countLit q [-37]) (count1306 q) 1 1 (meaningNeg35 q) (meaningNeg37 q) (meaning1307 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1307 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 37 = true ∨ valuation q 1307 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 1306 = false ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-32]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -37])
  have hm := merge_right (literal (valuationOf q) (1306)) (literal (valuationOf q) (1308)) (countLit q [-32]) (countLit q [-35, -37]) (count1308 q) 1 (meaning1306 q) (meaning1308 q) hs
  change valuationOf q 1306 = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 1306 = false ∨ valuation q 1308 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 1307 = false ∨ valuationOf q 1309 = true := by
  have hs : count1308 q = (countLit q [-32]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -37])
  have hm := merge_right (literal (valuationOf q) (1307)) (literal (valuationOf q) (1309)) (countLit q [-32]) (countLit q [-35, -37]) (count1308 q) 2 (meaning1307 q) (meaning1309 q) hs
  change valuationOf q 1307 = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 1307 = false ∨ valuation q 1309 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-32]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -37])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1308)) (countLit q [-32]) (countLit q [-35, -37]) (count1308 q) 1 (meaningNeg32 q) (meaning1308 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1308 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1306 = false ∨ valuationOf q 1309 = true := by
  have hs : count1308 q = (countLit q [-32]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -37])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1306)) (literal (valuationOf q) (1309)) (countLit q [-32]) (countLit q [-35, -37]) (count1308 q) 1 1 (meaningNeg32 q) (meaning1306 q) (meaning1309 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1306 = false ∨ valuation q 1309 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_right (literal (valuationOf q) (1308)) (literal (valuationOf q) (1311)) (countLit q [-27, -29, -30]) (countLit q [-32, -35, -37]) (count1311 q) 1 (meaning1308 q) (meaning1311 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1311 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1312 = true := by
  have hs : count1311 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_right (literal (valuationOf q) (1309)) (literal (valuationOf q) (1312)) (countLit q [-27, -29, -30]) (countLit q [-32, -35, -37]) (count1311 q) 2 (meaning1309 q) (meaning1312 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1312 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 1303 = false ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_left (literal (valuationOf q) (1303)) (literal (valuationOf q) (1311)) (countLit q [-27, -29, -30]) (countLit q [-32, -35, -37]) (count1311 q) 1 (meaning1303 q) (meaning1311 q) hs
  change valuationOf q 1303 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 1303 = false ∨ valuation q 1311 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 1303 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1312 = true := by
  have hs : count1311 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1303)) (literal (valuationOf q) (1308)) (literal (valuationOf q) (1312)) (countLit q [-27, -29, -30]) (countLit q [-32, -35, -37]) (count1311 q) 1 1 (meaning1303 q) (meaning1308 q) (meaning1312 q) hs
  change valuationOf q 1303 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 1303 = false ∨ valuation q 1308 = false ∨ valuation q 1312 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 1303 = false ∨ valuationOf q 1309 = false ∨ valuationOf q 1313 = true := by
  have hs : count1311 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1303)) (literal (valuationOf q) (1309)) (literal (valuationOf q) (1313)) (countLit q [-27, -29, -30]) (countLit q [-32, -35, -37]) (count1311 q) 1 2 (meaning1303 q) (meaning1309 q) (meaning1313 q) hs
  change valuationOf q 1303 = false ∨ valuationOf q 1309 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 1303 = false ∨ valuation q 1309 = false ∨ valuation q 1313 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1312 = true := by
  have hs : count1311 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_left (literal (valuationOf q) (1304)) (literal (valuationOf q) (1312)) (countLit q [-27, -29, -30]) (countLit q [-32, -35, -37]) (count1311 q) 2 (meaning1304 q) (meaning1312 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1312 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1313 = true := by
  have hs : count1311 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1304)) (literal (valuationOf q) (1308)) (literal (valuationOf q) (1313)) (countLit q [-27, -29, -30]) (countLit q [-32, -35, -37]) (count1311 q) 2 1 (meaning1304 q) (meaning1308 q) (meaning1313 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1308 = false ∨ valuation q 1313 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1309 = false ∨ valuationOf q 1314 = true := by
  have hs : count1311 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1304)) (literal (valuationOf q) (1309)) (literal (valuationOf q) (1314)) (countLit q [-27, -29, -30]) (countLit q [-32, -35, -37]) (count1311 q) 2 2 (meaning1304 q) (meaning1309 q) (meaning1314 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1309 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1309 = false ∨ valuation q 1314 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 1305 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1314 = true := by
  have hs : count1311 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1305)) (literal (valuationOf q) (1308)) (literal (valuationOf q) (1314)) (countLit q [-27, -29, -30]) (countLit q [-32, -35, -37]) (count1311 q) 3 1 (meaning1305 q) (meaning1308 q) (meaning1314 q) hs
  change valuationOf q 1305 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 1305 = false ∨ valuation q 1308 = false ∨ valuation q 1314 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1317)) (countLit q [-41]) (countLit q [-42]) (count1317 q) 1 (meaningNeg42 q) (meaning1317 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1317 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1317)) (countLit q [-41]) (countLit q [-42]) (count1317 q) 1 (meaningNeg41 q) (meaning1317 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1317 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1318 = true := by
  have hs : count1317 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1318)) (countLit q [-41]) (countLit q [-42]) (count1317 q) 1 1 (meaningNeg41 q) (meaningNeg42 q) (meaning1318 q) hs
  change (! (valuationOf q 41)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 42 = true ∨ valuation q 1318 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-40]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41, -42])
  have hm := merge_right (literal (valuationOf q) (1317)) (literal (valuationOf q) (1319)) (countLit q [-40]) (countLit q [-41, -42]) (count1319 q) 1 (meaning1317 q) (meaning1319 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1319 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 1318 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-40]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41, -42])
  have hm := merge_right (literal (valuationOf q) (1318)) (literal (valuationOf q) (1320)) (countLit q [-40]) (countLit q [-41, -42]) (count1319 q) 2 (meaning1318 q) (meaning1320 q) hs
  change valuationOf q 1318 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 1318 = false ∨ valuation q 1320 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-40]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41, -42])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1319)) (countLit q [-40]) (countLit q [-41, -42]) (count1319 q) 1 (meaningNeg40 q) (meaning1319 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1319 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1317 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-40]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41, -42])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (1317)) (literal (valuationOf q) (1320)) (countLit q [-40]) (countLit q [-41, -42]) (count1319 q) 1 1 (meaningNeg40 q) (meaning1317 q) (meaning1320 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1317 = false ∨ valuation q 1320 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1322 = true := by
  have hs : count1322 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1322)) (countLit q [-44]) (countLit q [-45]) (count1322 q) 1 (meaningNeg45 q) (meaning1322 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1322 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1322 = true := by
  have hs : count1322 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1322)) (countLit q [-44]) (countLit q [-45]) (count1322 q) 1 (meaningNeg44 q) (meaning1322 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1322 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 45 = true ∨ valuationOf q 1323 = true := by
  have hs : count1322 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (1323)) (countLit q [-44]) (countLit q [-45]) (count1322 q) 1 1 (meaningNeg44 q) (meaningNeg45 q) (meaning1323 q) hs
  change (! (valuationOf q 44)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 1323 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 45 = true ∨ valuation q 1323 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1324 = true := by
  have hs : count1324 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1324)) (countLit q [-48]) (countLit q [-49]) (count1324 q) 1 (meaningNeg49 q) (meaning1324 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1324 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1324 = true := by
  have hs : count1324 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1324)) (countLit q [-48]) (countLit q [-49]) (count1324 q) 1 (meaningNeg48 q) (meaning1324 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1324 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 49 = true ∨ valuationOf q 1325 = true := by
  have hs : count1324 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (1325)) (countLit q [-48]) (countLit q [-49]) (count1324 q) 1 1 (meaningNeg48 q) (meaningNeg49 q) (meaning1325 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 1325 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E091.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112091
