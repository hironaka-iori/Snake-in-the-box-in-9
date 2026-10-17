import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1154 = true := by
  have hs : count1133 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) + (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (l₂ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1121)) (literal (valuationOf q) (1154)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1133 q) 11 11 (meaning976 q) (meaning1121 q) (meaning1154 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1121 = false ∨ valuation q 1154 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1154 = true := by
  have hs : count1133 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) + (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (l₂ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1120)) (literal (valuationOf q) (1154)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1133 q) 12 10 (meaning977 q) (meaning1120 q) (meaning1154 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1120 = false ∨ valuation q 1154 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1154 = true := by
  have hs : count1133 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) + (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (l₂ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1119)) (literal (valuationOf q) (1154)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1133 q) 13 9 (meaning978 q) (meaning1119 q) (meaning1154 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1119 = false ∨ valuation q 1154 = true := counterClause1411 (baseVal q)

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1154 = false := by
  rw [value1154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1133 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1506 = true := by
  have hs : count1505 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1506)) (countLit q [-6]) (countLit q [-7]) (count1505 q) 1 1 (meaningNeg6 q) (meaningNeg7 q) (meaning1506 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 1506 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true := by
  have hs : count1507 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1509)) (countLit q [-2]) (countLit q [-6, -7]) (count1507 q) 1 2 (meaningNeg2 q) (meaning1506 q) (meaning1509 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1506 = false ∨ valuation q 1509 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 15 = true ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (1513)) (countLit q [-13]) (countLit q [-15]) (count1512 q) 1 1 (meaningNeg13 q) (meaningNeg15 q) (meaning1513 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 15 = true ∨ valuation q 1513 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-9, -10]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-13, -15])
  have hm := merge_right (literal (valuationOf q) (1513)) (literal (valuationOf q) (1515)) (countLit q [-9, -10]) (countLit q [-13, -15]) (count1514 q) 2 (meaning1513 q) (meaning1515 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1515 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-2, -6, -7]) + (countLit q [-9, -10, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-9, -10, -13, -15])
  have hm := merge_left (literal (valuationOf q) (1509)) (literal (valuationOf q) (1520)) (countLit q [-2, -6, -7]) (countLit q [-9, -10, -13, -15]) (count1518 q) 3 (meaning1509 q) (meaning1520 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1520 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1522 = true := by
  have hs : count1518 q = (countLit q [-2, -6, -7]) + (countLit q [-9, -10, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-9, -10, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1522)) (countLit q [-2, -6, -7]) (countLit q [-9, -10, -13, -15]) (count1518 q) 3 2 (meaning1509 q) (meaning1515 q) (meaning1522 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1515 = false ∨ valuation q 1522 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1528 = true := by
  have hs : count1527 q = (countLit q [-19]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1528)) (countLit q [-19]) (countLit q [-22]) (count1527 q) 1 1 (meaningNeg19 q) (meaningNeg22 q) (meaning1528 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 22 = true ∨ valuation q 1528 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-16, -17]) + (countLit q [-19, -22]) := List.countP_append (p := literal q) (l₁ := [-16, -17]) (l₂ := [-19, -22])
  have hm := merge_right (literal (valuationOf q) (1528)) (literal (valuationOf q) (1530)) (countLit q [-16, -17]) (countLit q [-19, -22]) (count1529 q) 2 (meaning1528 q) (meaning1530 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1530 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1533)) (countLit q [-25]) (countLit q [-26]) (count1533 q) 1 (meaningNeg26 q) (meaning1533 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1533 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1533)) (countLit q [-25]) (countLit q [-26]) (count1533 q) 1 (meaningNeg25 q) (meaning1533 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1533 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (1535)) (countLit q [-28]) (countLit q [-30]) (count1535 q) 1 (meaningNeg30 q) (meaning1535 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1535 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-25, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-25, -26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1538)) (countLit q [-25, -26]) (countLit q [-28, -30]) (count1537 q) 1 1 (meaning1533 q) (meaning1535 q) (meaning1538 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1535 = false ∨ valuation q 1538 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-16, -17, -19, -22]) + (countLit q [-25, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -19, -22]) (l₂ := [-25, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1538)) (literal (valuationOf q) (1542)) (countLit q [-16, -17, -19, -22]) (countLit q [-25, -26, -28, -30]) (count1541 q) 2 (meaning1538 q) (meaning1542 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1542 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-16, -17, -19, -22]) + (countLit q [-25, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -19, -22]) (l₂ := [-25, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1544)) (countLit q [-16, -17, -19, -22]) (countLit q [-25, -26, -28, -30]) (count1541 q) 2 2 (meaning1530 q) (meaning1538 q) (meaning1544 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1538 = false ∨ valuation q 1544 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1555 = true := by
  have hs : count1549 q = (countLit q [-2, -6, -7, -9, -10, -13, -15]) + (countLit q [-16, -17, -19, -22, -25, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -9, -10, -13, -15]) (l₂ := [-16, -17, -19, -22, -25, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1555)) (countLit q [-2, -6, -7, -9, -10, -13, -15]) (countLit q [-16, -17, -19, -22, -25, -26, -28, -30]) (count1549 q) 3 4 (meaning1520 q) (meaning1544 q) (meaning1555 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1544 = false ∨ valuation q 1555 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1555 = true := by
  have hs : count1549 q = (countLit q [-2, -6, -7, -9, -10, -13, -15]) + (countLit q [-16, -17, -19, -22, -25, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -9, -10, -13, -15]) (l₂ := [-16, -17, -19, -22, -25, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1555)) (countLit q [-2, -6, -7, -9, -10, -13, -15]) (countLit q [-16, -17, -19, -22, -25, -26, -28, -30]) (count1549 q) 5 2 (meaning1522 q) (meaning1542 q) (meaning1555 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1542 = false ∨ valuation q 1555 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1564)) (countLit q [-31]) (countLit q [-33]) (count1564 q) 1 (meaningNeg31 q) (meaning1564 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1564 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1566 = true := by
  have hs : count1566 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (1566)) (countLit q [-34]) (countLit q [-36]) (count1566 q) 1 (meaningNeg36 q) (meaning1566 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1566 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-31, -33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-31, -33]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1569)) (countLit q [-31, -33]) (countLit q [-34, -36]) (count1568 q) 1 1 (meaning1564 q) (meaning1566 q) (meaning1569 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1566 = false ∨ valuation q 1569 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1574 = true := by
  have hs : count1574 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1574)) (countLit q [-42]) (countLit q [-44]) (count1574 q) 1 (meaningNeg42 q) (meaning1574 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1574 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-40, -41]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-42, -44])
  have hm := merge_right (literal (valuationOf q) (1574)) (literal (valuationOf q) (1576)) (countLit q [-40, -41]) (countLit q [-42, -44]) (count1576 q) 1 (meaning1574 q) (meaning1576 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1576 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1582 = true := by
  have hs : count1580 q = (countLit q [-31, -33, -34, -36]) + (countLit q [-40, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36]) (l₂ := [-40, -41, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1582)) (countLit q [-31, -33, -34, -36]) (countLit q [-40, -41, -42, -44]) (count1580 q) 2 1 (meaning1569 q) (meaning1576 q) (meaning1582 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1576 = false ∨ valuation q 1582 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1596)) (countLit q [-56]) (countLit q [-58]) (count1596 q) 1 (meaningNeg58 q) (meaning1596 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1596 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-59]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (1598)) (countLit q [-59]) (countLit q [-62]) (count1598 q) 1 (meaningNeg62 q) (meaning1598 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1598 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-59]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1598)) (countLit q [-59]) (countLit q [-62]) (count1598 q) 1 (meaningNeg59 q) (meaning1598 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1598 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-56, -58]) + (countLit q [-59, -62]) := List.countP_append (p := literal q) (l₁ := [-56, -58]) (l₂ := [-59, -62])
  have hm := merge_right (literal (valuationOf q) (1598)) (literal (valuationOf q) (1600)) (countLit q [-56, -58]) (countLit q [-59, -62]) (count1600 q) 1 (meaning1598 q) (meaning1600 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1600 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-56, -58]) + (countLit q [-59, -62]) := List.countP_append (p := literal q) (l₁ := [-56, -58]) (l₂ := [-59, -62])
  have hm := merge_left (literal (valuationOf q) (1596)) (literal (valuationOf q) (1600)) (countLit q [-56, -58]) (countLit q [-59, -62]) (count1600 q) 1 (meaning1596 q) (meaning1600 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1600 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-48, -49, -50, -54]) + (countLit q [-56, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -54]) (l₂ := [-56, -58, -59, -62])
  have hm := merge_right (literal (valuationOf q) (1600)) (literal (valuationOf q) (1604)) (countLit q [-48, -49, -50, -54]) (countLit q [-56, -58, -59, -62]) (count1604 q) 1 (meaning1600 q) (meaning1604 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1604 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E153.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112153
