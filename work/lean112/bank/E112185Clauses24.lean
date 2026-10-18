import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-68]) + (countLit q [-71, -72]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-71, -72])
  have hm := merge_right (literal (valuationOf q) (1421)) (literal (valuationOf q) (1423)) (countLit q [-68]) (countLit q [-71, -72]) (count1423 q) 1 (meaning1421 q) (meaning1423 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1423 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-73]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1426)) (countLit q [-73]) (countLit q [-76]) (count1426 q) 1 (meaningNeg73 q) (meaning1426 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1426 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-73, -76]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-73, -76]) (l₂ := [-80, -82])
  have hm := merge_left (literal (valuationOf q) (1426)) (literal (valuationOf q) (1430)) (countLit q [-73, -76]) (countLit q [-80, -82]) (count1430 q) 1 (meaning1426 q) (meaning1430 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1430 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-68, -71, -72]) + (countLit q [-73, -76, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-68, -71, -72]) (l₂ := [-73, -76, -80, -82])
  have hm := merge_right (literal (valuationOf q) (1430)) (literal (valuationOf q) (1434)) (countLit q [-68, -71, -72]) (countLit q [-73, -76, -80, -82]) (count1434 q) 1 (meaning1430 q) (meaning1434 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1434 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-68, -71, -72]) + (countLit q [-73, -76, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-68, -71, -72]) (l₂ := [-73, -76, -80, -82])
  have hm := merge_left (literal (valuationOf q) (1423)) (literal (valuationOf q) (1434)) (countLit q [-68, -71, -72]) (countLit q [-73, -76, -80, -82]) (count1434 q) 1 (meaning1423 q) (meaning1434 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1434 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-57, -58, -60, -63, -65, -66]) + (countLit q [-68, -71, -72, -73, -76, -80, -82]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -60, -63, -65, -66]) (l₂ := [-68, -71, -72, -73, -76, -80, -82])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1442)) (countLit q [-57, -58, -60, -63, -65, -66]) (countLit q [-68, -71, -72, -73, -76, -80, -82]) (count1441 q) 1 1 (meaning1415 q) (meaning1434 q) (meaning1442 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1434 = false ∨ valuation q 1442 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1453 = true := by
  have hs : count1453 q = (countLit q [-84]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1453)) (countLit q [-84]) (countLit q [-87]) (count1453 q) 1 (meaningNeg84 q) (meaning1453 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1453 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1455 = true := by
  have hs : count1455 q = (countLit q [-83]) + (countLit q [-84, -87]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84, -87])
  have hm := merge_right (literal (valuationOf q) (1453)) (literal (valuationOf q) (1455)) (countLit q [-83]) (countLit q [-84, -87]) (count1455 q) 1 (meaning1453 q) (meaning1455 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1455 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-83, -84, -87]) + (countLit q [-89, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -84, -87]) (l₂ := [-89, -91, -94])
  have hm := merge_left (literal (valuationOf q) (1455)) (literal (valuationOf q) (1463)) (countLit q [-83, -84, -87]) (countLit q [-89, -91, -94]) (count1463 q) 1 (meaning1455 q) (meaning1463 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1463 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1474)) (countLit q [-102]) (countLit q [-104]) (count1474 q) 1 (meaningNeg104 q) (meaning1474 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1474 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-105]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-105)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1477)) (countLit q [-105]) (countLit q [-107]) (count1476 q) 1 1 (meaningNeg105 q) (meaningNeg107 q) (meaning1477 q) hs
  change (! (valuationOf q 105)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 107 = true ∨ valuation q 1477 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1480 = true := by
  have hs : count1478 q = (countLit q [-102, -104]) + (countLit q [-105, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -104]) (l₂ := [-105, -107])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1480)) (countLit q [-102, -104]) (countLit q [-105, -107]) (count1478 q) 1 2 (meaning1474 q) (meaning1477 q) (meaning1480 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1477 = false ∨ valuation q 1480 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1484 = true := by
  have hs : count1482 q = (countLit q [-96, -97, -99]) + (countLit q [-102, -104, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -99]) (l₂ := [-102, -104, -105, -107])
  have hm := merge_right (literal (valuationOf q) (1480)) (literal (valuationOf q) (1484)) (countLit q [-96, -97, -99]) (countLit q [-102, -104, -105, -107]) (count1482 q) 3 (meaning1480 q) (meaning1484 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1484 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1492 = true := by
  have hs : count1489 q = (countLit q [-83, -84, -87, -89, -91, -94]) + (countLit q [-96, -97, -99, -102, -104, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-83, -84, -87, -89, -91, -94]) (l₂ := [-96, -97, -99, -102, -104, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1492)) (countLit q [-83, -84, -87, -89, -91, -94]) (countLit q [-96, -97, -99, -102, -104, -105, -107]) (count1489 q) 1 3 (meaning1463 q) (meaning1484 q) (meaning1492 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1484 = false ∨ valuation q 1492 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1506 = true := by
  have hs : count1501 q = (countLit q [-57, -58, -60, -63, -65, -66, -68, -71, -72, -73, -76, -80, -82]) + (countLit q [-83, -84, -87, -89, -91, -94, -96, -97, -99, -102, -104, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -60, -63, -65, -66, -68, -71, -72, -73, -76, -80, -82]) (l₂ := [-83, -84, -87, -89, -91, -94, -96, -97, -99, -102, -104, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1506)) (countLit q [-57, -58, -60, -63, -65, -66, -68, -71, -72, -73, -76, -80, -82]) (countLit q [-83, -84, -87, -89, -91, -94, -96, -97, -99, -102, -104, -105, -107]) (count1501 q) 2 4 (meaning1442 q) (meaning1492 q) (meaning1506 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1492 = false ∨ valuation q 1506 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1524 = true := by
  have hs : count1513 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28, -30, -33, -35, -36, -38, -41, -42, -44, -47, -49, -50, -52, -55]) + (countLit q [-57, -58, -60, -63, -65, -66, -68, -71, -72, -73, -76, -80, -82, -83, -84, -87, -89, -91, -94, -96, -97, -99, -102, -104, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28, -30, -33, -35, -36, -38, -41, -42, -44, -47, -49, -50, -52, -55]) (l₂ := [-57, -58, -60, -63, -65, -66, -68, -71, -72, -73, -76, -80, -82, -83, -84, -87, -89, -91, -94, -96, -97, -99, -102, -104, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1398)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1524)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28, -30, -33, -35, -36, -38, -41, -42, -44, -47, -49, -50, -52, -55]) (countLit q [-57, -58, -60, -63, -65, -66, -68, -71, -72, -73, -76, -80, -82, -83, -84, -87, -89, -91, -94, -96, -97, -99, -102, -104, -105, -107]) (count1513 q) 6 6 (meaning1398 q) (meaning1506 q) (meaning1524 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1506 = false ∨ valuation q 1524 = true := counterClause784 (baseVal q)

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false := by
  rw [value1524]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1513 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 4 = false := by
  rw [value1, value2, value3, value4]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (2 : Vertex) (3 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 10 = false ∨ valuation q 11 = false := by
  rw [value1, value2, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (16 : Vertex) (17 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 14 = false := by
  rw [value3, value6, value12, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (2 : Vertex) (6 : Vertex) (18 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 19 = false := by
  rw [value8, value9, value17, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (13 : Vertex) (15 : Vertex) (29 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 13 = false := by
  rw [value10, value11, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (16 : Vertex) (17 : Vertex) (18 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value10, value15, value62, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (16 : Vertex) (24 : Vertex) (272 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 19 = false := by
  rw [value16, value17, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (28 : Vertex) (29 : Vertex) (30 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value32, value33, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value38, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value54, value55, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (259 : Vertex) (266 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value93, value94, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (450 : Vertex) (451 : Vertex) (458 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E185.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h⟩

end
end Snake9.Regrowth.E112185
