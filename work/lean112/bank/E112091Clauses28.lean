import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1474 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1404)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1474)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 6 4 (meaning1404 q) (meaning1455 q) (meaning1474 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1455 = false ∨ valuation q 1474 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1472)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 7 1 (meaning1405 q) (meaning1452 q) (meaning1472 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1452 = false ∨ valuation q 1472 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1473 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1473)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 7 2 (meaning1405 q) (meaning1453 q) (meaning1473 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1453 = false ∨ valuation q 1473 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1406)) (literal (valuationOf q) (1472)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 8 (meaning1406 q) (meaning1472 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1472 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1473 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1473)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 8 1 (meaning1406 q) (meaning1452 q) (meaning1473 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1452 = false ∨ valuation q 1473 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) + (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (l₂ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1352)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1478 q) 3 10 (meaning1352 q) (meaning1474 q) (meaning1490 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1474 = false ∨ valuation q 1490 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) + (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (l₂ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1478 q) 4 9 (meaning1353 q) (meaning1473 q) (meaning1490 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1473 = false ∨ valuation q 1490 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) + (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (l₂ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1478 q) 5 8 (meaning1354 q) (meaning1472 q) (meaning1490 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1472 = false ∨ valuation q 1490 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) + (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (l₂ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1478 q) 6 7 (meaning1355 q) (meaning1471 q) (meaning1490 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1471 = false ∨ valuation q 1490 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) + (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (l₂ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1356)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1478 q) 7 6 (meaning1356 q) (meaning1470 q) (meaning1490 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1470 = false ∨ valuation q 1490 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) + (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (l₂ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1478 q) 8 5 (meaning1357 q) (meaning1469 q) (meaning1490 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1469 = false ∨ valuation q 1490 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) + (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (l₂ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1358)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1478 q) 9 4 (meaning1358 q) (meaning1468 q) (meaning1490 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1468 = false ∨ valuation q 1490 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1490 = true := by
  have hs : count1478 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) + (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (l₂ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1359)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1478 q) 10 3 (meaning1359 q) (meaning1467 q) (meaning1490 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1467 = false ∨ valuation q 1490 = true := counterClause909 (baseVal q)

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false := by
  rw [value1490]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1478 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false := by
  rw [value4, value5, value6, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (8 : Vertex) (9 : Vertex) (10 : Vertex) (11 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value4, value5, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (8 : Vertex) (9 : Vertex) (72 : Vertex) (73 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value5, value7, value14, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (9 : Vertex) (11 : Vertex) (25 : Vertex) (27 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 32 = false ∨ valuation q 33 = false := by
  rw [value24, value25, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (78 : Vertex) (79 : Vertex) (94 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 57 = false ∨ valuation q 58 = false := by
  rw [value34, value37, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (224 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value35, value36, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (164 : Vertex) (166 : Vertex) (180 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 47 = false ∨ valuation q 49 = false := by
  rw [value37, value39, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (168 : Vertex) (170 : Vertex) (184 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value82, value83, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (430 : Vertex) (431 : Vertex) (446 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E091.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h⟩

end
end Snake9.Regrowth.E112091
