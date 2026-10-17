import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1088 = true := by
  have hs : count1070 q = (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26, -27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) + (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88, -90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26, -27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) (l₂ := [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88, -90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1088)) (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26, -27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88, -90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) (count1070 q) 11 8 (meaning924 q) (meaning1058 q) (meaning1088 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 1058 = false ∨ valuation q 1088 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1088 = true := by
  have hs : count1070 q = (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26, -27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) + (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88, -90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26, -27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) (l₂ := [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88, -90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1088)) (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26, -27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88, -90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) (count1070 q) 12 7 (meaning925 q) (meaning1057 q) (meaning1088 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 1057 = false ∨ valuation q 1088 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1088 = true := by
  have hs : count1070 q = (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26, -27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) + (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88, -90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26, -27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) (l₂ := [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88, -90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116])
  have hm := merge_two (literal (valuationOf q) (926)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1088)) (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26, -27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88, -90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) (count1070 q) 13 6 (meaning926 q) (meaning1056 q) (meaning1088 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 1056 = false ∨ valuation q 1088 = true := counterClause995 (baseVal q)

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1088 = false := by
  rw [value1088]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1070 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause997 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1421)) (countLit q [-6]) (countLit q [-7]) (count1421 q) 1 (meaningNeg7 q) (meaning1421 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1421 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1421)) (countLit q [-6]) (countLit q [-7]) (count1421 q) 1 (meaningNeg6 q) (meaning1421 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1421 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1422 = true := by
  have hs : count1421 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1422)) (countLit q [-6]) (countLit q [-7]) (count1421 q) 1 1 (meaningNeg6 q) (meaningNeg7 q) (meaning1422 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 1422 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-3]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6, -7])
  have hm := merge_right (literal (valuationOf q) (1421)) (literal (valuationOf q) (1423)) (countLit q [-3]) (countLit q [-6, -7]) (count1423 q) 1 (meaning1421 q) (meaning1423 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1423 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1424 = true := by
  have hs : count1423 q = (countLit q [-3]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6, -7])
  have hm := merge_right (literal (valuationOf q) (1422)) (literal (valuationOf q) (1424)) (countLit q [-3]) (countLit q [-6, -7]) (count1423 q) 2 (meaning1422 q) (meaning1424 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1424 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-3]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6, -7])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1423)) (countLit q [-3]) (countLit q [-6, -7]) (count1423 q) 1 (meaningNeg3 q) (meaning1423 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1423 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1421 = false ∨ valuationOf q 1424 = true := by
  have hs : count1423 q = (countLit q [-3]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1424)) (countLit q [-3]) (countLit q [-6, -7]) (count1423 q) 1 1 (meaningNeg3 q) (meaning1421 q) (meaning1424 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1421 = false ∨ valuation q 1424 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1422 = false ∨ valuationOf q 1425 = true := by
  have hs : count1423 q = (countLit q [-3]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1425)) (countLit q [-3]) (countLit q [-6, -7]) (count1423 q) 1 2 (meaningNeg3 q) (meaning1422 q) (meaning1425 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1422 = false ∨ valuation q 1425 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (1426)) (countLit q [-9]) (countLit q [-11]) (count1426 q) 1 (meaningNeg11 q) (meaning1426 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1426 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (1426)) (countLit q [-9]) (countLit q [-11]) (count1426 q) 1 (meaningNeg9 q) (meaning1426 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1426 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 11 = true ∨ valuationOf q 1427 = true := by
  have hs : count1426 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-11)) (literal (valuationOf q) (1427)) (countLit q [-9]) (countLit q [-11]) (count1426 q) 1 1 (meaningNeg9 q) (meaningNeg11 q) (meaning1427 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 11)) = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 11 = true ∨ valuation q 1427 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-13]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1428)) (countLit q [-13]) (countLit q [-17]) (count1428 q) 1 (meaningNeg17 q) (meaning1428 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1428 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-13]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1428)) (countLit q [-13]) (countLit q [-17]) (count1428 q) 1 (meaningNeg13 q) (meaning1428 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1428 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 17 = true ∨ valuationOf q 1429 = true := by
  have hs : count1428 q = (countLit q [-13]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (1429)) (countLit q [-13]) (countLit q [-17]) (count1428 q) 1 1 (meaningNeg13 q) (meaningNeg17 q) (meaning1429 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 17 = true ∨ valuation q 1429 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-9, -11]) + (countLit q [-13, -17]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -17])
  have hm := merge_right (literal (valuationOf q) (1428)) (literal (valuationOf q) (1430)) (countLit q [-9, -11]) (countLit q [-13, -17]) (count1430 q) 1 (meaning1428 q) (meaning1430 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1430 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-9, -11]) + (countLit q [-13, -17]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -17])
  have hm := merge_right (literal (valuationOf q) (1429)) (literal (valuationOf q) (1431)) (countLit q [-9, -11]) (countLit q [-13, -17]) (count1430 q) 2 (meaning1429 q) (meaning1431 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1431 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-9, -11]) + (countLit q [-13, -17]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -17])
  have hm := merge_left (literal (valuationOf q) (1426)) (literal (valuationOf q) (1430)) (countLit q [-9, -11]) (countLit q [-13, -17]) (count1430 q) 1 (meaning1426 q) (meaning1430 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1430 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-9, -11]) + (countLit q [-13, -17]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -17])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1431)) (countLit q [-9, -11]) (countLit q [-13, -17]) (count1430 q) 1 1 (meaning1426 q) (meaning1428 q) (meaning1431 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1428 = false ∨ valuation q 1431 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1432 = true := by
  have hs : count1430 q = (countLit q [-9, -11]) + (countLit q [-13, -17]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -17])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1432)) (countLit q [-9, -11]) (countLit q [-13, -17]) (count1430 q) 1 2 (meaning1426 q) (meaning1429 q) (meaning1432 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1429 = false ∨ valuation q 1432 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-9, -11]) + (countLit q [-13, -17]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -17])
  have hm := merge_left (literal (valuationOf q) (1427)) (literal (valuationOf q) (1431)) (countLit q [-9, -11]) (countLit q [-13, -17]) (count1430 q) 2 (meaning1427 q) (meaning1431 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1431 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1432 = true := by
  have hs : count1430 q = (countLit q [-9, -11]) + (countLit q [-13, -17]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -17])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1432)) (countLit q [-9, -11]) (countLit q [-13, -17]) (count1430 q) 2 1 (meaning1427 q) (meaning1428 q) (meaning1432 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1428 = false ∨ valuation q 1432 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1433 = true := by
  have hs : count1430 q = (countLit q [-9, -11]) + (countLit q [-13, -17]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-13, -17])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1433)) (countLit q [-9, -11]) (countLit q [-13, -17]) (count1430 q) 2 2 (meaning1427 q) (meaning1429 q) (meaning1433 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1429 = false ∨ valuation q 1433 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_right (literal (valuationOf q) (1430)) (literal (valuationOf q) (1434)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 1 (meaning1430 q) (meaning1434 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1434 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_right (literal (valuationOf q) (1431)) (literal (valuationOf q) (1435)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 2 (meaning1431 q) (meaning1435 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1435 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_right (literal (valuationOf q) (1432)) (literal (valuationOf q) (1436)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 3 (meaning1432 q) (meaning1436 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1436 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1437 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_right (literal (valuationOf q) (1433)) (literal (valuationOf q) (1437)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 4 (meaning1433 q) (meaning1437 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1437 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_left (literal (valuationOf q) (1423)) (literal (valuationOf q) (1434)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 1 (meaning1423 q) (meaning1434 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1434 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1435)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 1 1 (meaning1423 q) (meaning1430 q) (meaning1435 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1430 = false ∨ valuation q 1435 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E158.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112158
