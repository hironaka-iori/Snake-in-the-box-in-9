import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1360 = true := by
  have hs : count1360 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1360)) (countLit q [-75]) (countLit q [-77]) (count1360 q) 1 (meaningNeg77 q) (meaning1360 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1360 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1360 = true := by
  have hs : count1360 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1360)) (countLit q [-75]) (countLit q [-77]) (count1360 q) 1 (meaningNeg75 q) (meaning1360 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1360 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1361 = true := by
  have hs : count1360 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1361)) (countLit q [-75]) (countLit q [-77]) (count1360 q) 1 1 (meaningNeg75 q) (meaningNeg77 q) (meaning1361 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 1361 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-71]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-75, -77])
  have hm := merge_right (literal (valuationOf q) (1360)) (literal (valuationOf q) (1362)) (countLit q [-71]) (countLit q [-75, -77]) (count1362 q) 1 (meaning1360 q) (meaning1362 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1362 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-71]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-75, -77])
  have hm := merge_right (literal (valuationOf q) (1361)) (literal (valuationOf q) (1363)) (countLit q [-71]) (countLit q [-75, -77]) (count1362 q) 2 (meaning1361 q) (meaning1363 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1363 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-71]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-75, -77])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1362)) (countLit q [-71]) (countLit q [-75, -77]) (count1362 q) 1 (meaningNeg71 q) (meaning1362 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1362 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1360 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-71]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-75, -77])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (1360)) (literal (valuationOf q) (1363)) (countLit q [-71]) (countLit q [-75, -77]) (count1362 q) 1 1 (meaningNeg71 q) (meaning1360 q) (meaning1363 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1360 = false ∨ valuation q 1363 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-68, -69, -70]) + (countLit q [-71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-68, -69, -70]) (l₂ := [-71, -75, -77])
  have hm := merge_right (literal (valuationOf q) (1362)) (literal (valuationOf q) (1365)) (countLit q [-68, -69, -70]) (countLit q [-71, -75, -77]) (count1365 q) 1 (meaning1362 q) (meaning1365 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1365 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-68, -69, -70]) + (countLit q [-71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-68, -69, -70]) (l₂ := [-71, -75, -77])
  have hm := merge_right (literal (valuationOf q) (1363)) (literal (valuationOf q) (1366)) (countLit q [-68, -69, -70]) (countLit q [-71, -75, -77]) (count1365 q) 2 (meaning1363 q) (meaning1366 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1366 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-68, -69, -70]) + (countLit q [-71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-68, -69, -70]) (l₂ := [-71, -75, -77])
  have hm := merge_left (literal (valuationOf q) (1357)) (literal (valuationOf q) (1365)) (countLit q [-68, -69, -70]) (countLit q [-71, -75, -77]) (count1365 q) 1 (meaning1357 q) (meaning1365 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1365 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-68, -69, -70]) + (countLit q [-71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-68, -69, -70]) (l₂ := [-71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1366)) (countLit q [-68, -69, -70]) (countLit q [-71, -75, -77]) (count1365 q) 1 1 (meaning1357 q) (meaning1362 q) (meaning1366 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1362 = false ∨ valuation q 1366 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1367 = true := by
  have hs : count1365 q = (countLit q [-68, -69, -70]) + (countLit q [-71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-68, -69, -70]) (l₂ := [-71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1367)) (countLit q [-68, -69, -70]) (countLit q [-71, -75, -77]) (count1365 q) 1 2 (meaning1357 q) (meaning1363 q) (meaning1367 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1363 = false ∨ valuation q 1367 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-68, -69, -70]) + (countLit q [-71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-68, -69, -70]) (l₂ := [-71, -75, -77])
  have hm := merge_left (literal (valuationOf q) (1358)) (literal (valuationOf q) (1366)) (countLit q [-68, -69, -70]) (countLit q [-71, -75, -77]) (count1365 q) 2 (meaning1358 q) (meaning1366 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1366 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1367 = true := by
  have hs : count1365 q = (countLit q [-68, -69, -70]) + (countLit q [-71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-68, -69, -70]) (l₂ := [-71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1358)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1367)) (countLit q [-68, -69, -70]) (countLit q [-71, -75, -77]) (count1365 q) 2 1 (meaning1358 q) (meaning1362 q) (meaning1367 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1362 = false ∨ valuation q 1367 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1371 = true := by
  have hs : count1371 q = (countLit q [-54, -55, -59, -61, -62, -64]) + (countLit q [-68, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64]) (l₂ := [-68, -69, -70, -71, -75, -77])
  have hm := merge_right (literal (valuationOf q) (1365)) (literal (valuationOf q) (1371)) (countLit q [-54, -55, -59, -61, -62, -64]) (countLit q [-68, -69, -70, -71, -75, -77]) (count1371 q) 1 (meaning1365 q) (meaning1371 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1371 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1372 = true := by
  have hs : count1371 q = (countLit q [-54, -55, -59, -61, -62, -64]) + (countLit q [-68, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64]) (l₂ := [-68, -69, -70, -71, -75, -77])
  have hm := merge_right (literal (valuationOf q) (1366)) (literal (valuationOf q) (1372)) (countLit q [-54, -55, -59, -61, -62, -64]) (countLit q [-68, -69, -70, -71, -75, -77]) (count1371 q) 2 (meaning1366 q) (meaning1372 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1372 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1373 = true := by
  have hs : count1371 q = (countLit q [-54, -55, -59, -61, -62, -64]) + (countLit q [-68, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64]) (l₂ := [-68, -69, -70, -71, -75, -77])
  have hm := merge_right (literal (valuationOf q) (1367)) (literal (valuationOf q) (1373)) (countLit q [-54, -55, -59, -61, -62, -64]) (countLit q [-68, -69, -70, -71, -75, -77]) (count1371 q) 3 (meaning1367 q) (meaning1373 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1373 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1372 = true := by
  have hs : count1371 q = (countLit q [-54, -55, -59, -61, -62, -64]) + (countLit q [-68, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64]) (l₂ := [-68, -69, -70, -71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1365)) (literal (valuationOf q) (1372)) (countLit q [-54, -55, -59, -61, -62, -64]) (countLit q [-68, -69, -70, -71, -75, -77]) (count1371 q) 1 1 (meaning1349 q) (meaning1365 q) (meaning1372 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1365 = false ∨ valuation q 1372 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1366 = false ∨ valuationOf q 1373 = true := by
  have hs : count1371 q = (countLit q [-54, -55, -59, -61, -62, -64]) + (countLit q [-68, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64]) (l₂ := [-68, -69, -70, -71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1366)) (literal (valuationOf q) (1373)) (countLit q [-54, -55, -59, -61, -62, -64]) (countLit q [-68, -69, -70, -71, -75, -77]) (count1371 q) 1 2 (meaning1349 q) (meaning1366 q) (meaning1373 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1366 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1366 = false ∨ valuation q 1373 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1374 = true := by
  have hs : count1371 q = (countLit q [-54, -55, -59, -61, -62, -64]) + (countLit q [-68, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64]) (l₂ := [-68, -69, -70, -71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1374)) (countLit q [-54, -55, -59, -61, -62, -64]) (countLit q [-68, -69, -70, -71, -75, -77]) (count1371 q) 1 3 (meaning1349 q) (meaning1367 q) (meaning1374 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1367 = false ∨ valuation q 1374 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1373 = true := by
  have hs : count1371 q = (countLit q [-54, -55, -59, -61, -62, -64]) + (countLit q [-68, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64]) (l₂ := [-68, -69, -70, -71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1350)) (literal (valuationOf q) (1365)) (literal (valuationOf q) (1373)) (countLit q [-54, -55, -59, -61, -62, -64]) (countLit q [-68, -69, -70, -71, -75, -77]) (count1371 q) 2 1 (meaning1350 q) (meaning1365 q) (meaning1373 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1365 = false ∨ valuation q 1373 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1366 = false ∨ valuationOf q 1374 = true := by
  have hs : count1371 q = (countLit q [-54, -55, -59, -61, -62, -64]) + (countLit q [-68, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64]) (l₂ := [-68, -69, -70, -71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1350)) (literal (valuationOf q) (1366)) (literal (valuationOf q) (1374)) (countLit q [-54, -55, -59, -61, -62, -64]) (countLit q [-68, -69, -70, -71, -75, -77]) (count1371 q) 2 2 (meaning1350 q) (meaning1366 q) (meaning1374 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1366 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1366 = false ∨ valuation q 1374 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1374 = true := by
  have hs : count1371 q = (countLit q [-54, -55, -59, -61, -62, -64]) + (countLit q [-68, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64]) (l₂ := [-68, -69, -70, -71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1365)) (literal (valuationOf q) (1374)) (countLit q [-54, -55, -59, -61, -62, -64]) (countLit q [-68, -69, -70, -71, -75, -77]) (count1371 q) 3 1 (meaning1351 q) (meaning1365 q) (meaning1374 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1365 = false ∨ valuation q 1374 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1381)) (countLit q [-80]) (countLit q [-81]) (count1381 q) 1 (meaningNeg81 q) (meaning1381 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1381 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1381)) (countLit q [-80]) (countLit q [-81]) (count1381 q) 1 (meaningNeg80 q) (meaning1381 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1381 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1382 = true := by
  have hs : count1381 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1382)) (countLit q [-80]) (countLit q [-81]) (count1381 q) 1 1 (meaningNeg80 q) (meaningNeg81 q) (meaning1382 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 1382 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-79]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80, -81])
  have hm := merge_right (literal (valuationOf q) (1381)) (literal (valuationOf q) (1383)) (countLit q [-79]) (countLit q [-80, -81]) (count1383 q) 1 (meaning1381 q) (meaning1383 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1383 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-79]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80, -81])
  have hm := merge_right (literal (valuationOf q) (1382)) (literal (valuationOf q) (1384)) (countLit q [-79]) (countLit q [-80, -81]) (count1383 q) 2 (meaning1382 q) (meaning1384 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1384 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-79]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80, -81])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1383)) (countLit q [-79]) (countLit q [-80, -81]) (count1383 q) 1 (meaningNeg79 q) (meaning1383 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1383 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-79]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80, -81])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1384)) (countLit q [-79]) (countLit q [-80, -81]) (count1383 q) 1 1 (meaningNeg79 q) (meaning1381 q) (meaning1384 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1381 = false ∨ valuation q 1384 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1382 = false ∨ valuationOf q 1385 = true := by
  have hs : count1383 q = (countLit q [-79]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80, -81])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1385)) (countLit q [-79]) (countLit q [-80, -81]) (count1383 q) 1 2 (meaningNeg79 q) (meaning1382 q) (meaning1385 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1382 = false ∨ valuation q 1385 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1386)) (countLit q [-87]) (countLit q [-90]) (count1386 q) 1 (meaningNeg90 q) (meaning1386 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1386 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E175.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112175
