import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-44, -45]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-48, -49])
  have hm := merge_right (literal (valuationOf q) (1324)) (literal (valuationOf q) (1326)) (countLit q [-44, -45]) (countLit q [-48, -49]) (count1326 q) 1 (meaning1324 q) (meaning1326 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1326 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 1325 = false ∨ valuationOf q 1327 = true := by
  have hs : count1326 q = (countLit q [-44, -45]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-48, -49])
  have hm := merge_right (literal (valuationOf q) (1325)) (literal (valuationOf q) (1327)) (countLit q [-44, -45]) (countLit q [-48, -49]) (count1326 q) 2 (meaning1325 q) (meaning1327 q) hs
  change valuationOf q 1325 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 1325 = false ∨ valuation q 1327 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-44, -45]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-48, -49])
  have hm := merge_left (literal (valuationOf q) (1322)) (literal (valuationOf q) (1326)) (countLit q [-44, -45]) (countLit q [-48, -49]) (count1326 q) 1 (meaning1322 q) (meaning1326 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1326 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1327 = true := by
  have hs : count1326 q = (countLit q [-44, -45]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-48, -49])
  have hm := merge_two (literal (valuationOf q) (1322)) (literal (valuationOf q) (1324)) (literal (valuationOf q) (1327)) (countLit q [-44, -45]) (countLit q [-48, -49]) (count1326 q) 1 1 (meaning1322 q) (meaning1324 q) (meaning1327 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1324 = false ∨ valuation q 1327 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1325 = false ∨ valuationOf q 1328 = true := by
  have hs : count1326 q = (countLit q [-44, -45]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-48, -49])
  have hm := merge_two (literal (valuationOf q) (1322)) (literal (valuationOf q) (1325)) (literal (valuationOf q) (1328)) (countLit q [-44, -45]) (countLit q [-48, -49]) (count1326 q) 1 2 (meaning1322 q) (meaning1325 q) (meaning1328 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1325 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1325 = false ∨ valuation q 1328 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1327 = true := by
  have hs : count1326 q = (countLit q [-44, -45]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-48, -49])
  have hm := merge_left (literal (valuationOf q) (1323)) (literal (valuationOf q) (1327)) (countLit q [-44, -45]) (countLit q [-48, -49]) (count1326 q) 2 (meaning1323 q) (meaning1327 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1327 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1328 = true := by
  have hs : count1326 q = (countLit q [-44, -45]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-48, -49])
  have hm := merge_two (literal (valuationOf q) (1323)) (literal (valuationOf q) (1324)) (literal (valuationOf q) (1328)) (countLit q [-44, -45]) (countLit q [-48, -49]) (count1326 q) 2 1 (meaning1323 q) (meaning1324 q) (meaning1328 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1324 = false ∨ valuation q 1328 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1325 = false ∨ valuationOf q 1329 = true := by
  have hs : count1326 q = (countLit q [-44, -45]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-48, -49])
  have hm := merge_two (literal (valuationOf q) (1323)) (literal (valuationOf q) (1325)) (literal (valuationOf q) (1329)) (countLit q [-44, -45]) (countLit q [-48, -49]) (count1326 q) 2 2 (meaning1323 q) (meaning1325 q) (meaning1329 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1325 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1325 = false ∨ valuation q 1329 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-40, -41, -42]) + (countLit q [-44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -42]) (l₂ := [-44, -45, -48, -49])
  have hm := merge_right (literal (valuationOf q) (1326)) (literal (valuationOf q) (1330)) (countLit q [-40, -41, -42]) (countLit q [-44, -45, -48, -49]) (count1330 q) 1 (meaning1326 q) (meaning1330 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1330 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1331 = true := by
  have hs : count1330 q = (countLit q [-40, -41, -42]) + (countLit q [-44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -42]) (l₂ := [-44, -45, -48, -49])
  have hm := merge_right (literal (valuationOf q) (1327)) (literal (valuationOf q) (1331)) (countLit q [-40, -41, -42]) (countLit q [-44, -45, -48, -49]) (count1330 q) 2 (meaning1327 q) (meaning1331 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1331 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1332 = true := by
  have hs : count1330 q = (countLit q [-40, -41, -42]) + (countLit q [-44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -42]) (l₂ := [-44, -45, -48, -49])
  have hm := merge_right (literal (valuationOf q) (1328)) (literal (valuationOf q) (1332)) (countLit q [-40, -41, -42]) (countLit q [-44, -45, -48, -49]) (count1330 q) 3 (meaning1328 q) (meaning1332 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1332 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1333 = true := by
  have hs : count1330 q = (countLit q [-40, -41, -42]) + (countLit q [-44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -42]) (l₂ := [-44, -45, -48, -49])
  have hm := merge_right (literal (valuationOf q) (1329)) (literal (valuationOf q) (1333)) (countLit q [-40, -41, -42]) (countLit q [-44, -45, -48, -49]) (count1330 q) 4 (meaning1329 q) (meaning1333 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1333 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-40, -41, -42]) + (countLit q [-44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -42]) (l₂ := [-44, -45, -48, -49])
  have hm := merge_left (literal (valuationOf q) (1319)) (literal (valuationOf q) (1330)) (countLit q [-40, -41, -42]) (countLit q [-44, -45, -48, -49]) (count1330 q) 1 (meaning1319 q) (meaning1330 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1330 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1331 = true := by
  have hs : count1330 q = (countLit q [-40, -41, -42]) + (countLit q [-44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -42]) (l₂ := [-44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1326)) (literal (valuationOf q) (1331)) (countLit q [-40, -41, -42]) (countLit q [-44, -45, -48, -49]) (count1330 q) 1 1 (meaning1319 q) (meaning1326 q) (meaning1331 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1326 = false ∨ valuation q 1331 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1332 = true := by
  have hs : count1330 q = (countLit q [-40, -41, -42]) + (countLit q [-44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -42]) (l₂ := [-44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1327)) (literal (valuationOf q) (1332)) (countLit q [-40, -41, -42]) (countLit q [-44, -45, -48, -49]) (count1330 q) 1 2 (meaning1319 q) (meaning1327 q) (meaning1332 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1327 = false ∨ valuation q 1332 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1333 = true := by
  have hs : count1330 q = (countLit q [-40, -41, -42]) + (countLit q [-44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -42]) (l₂ := [-44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1328)) (literal (valuationOf q) (1333)) (countLit q [-40, -41, -42]) (countLit q [-44, -45, -48, -49]) (count1330 q) 1 3 (meaning1319 q) (meaning1328 q) (meaning1333 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1328 = false ∨ valuation q 1333 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1329 = false ∨ valuationOf q 1334 = true := by
  have hs : count1330 q = (countLit q [-40, -41, -42]) + (countLit q [-44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -42]) (l₂ := [-44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1329)) (literal (valuationOf q) (1334)) (countLit q [-40, -41, -42]) (countLit q [-44, -45, -48, -49]) (count1330 q) 1 4 (meaning1319 q) (meaning1329 q) (meaning1334 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1329 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1329 = false ∨ valuation q 1334 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1331 = true := by
  have hs : count1330 q = (countLit q [-40, -41, -42]) + (countLit q [-44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -42]) (l₂ := [-44, -45, -48, -49])
  have hm := merge_left (literal (valuationOf q) (1320)) (literal (valuationOf q) (1331)) (countLit q [-40, -41, -42]) (countLit q [-44, -45, -48, -49]) (count1330 q) 2 (meaning1320 q) (meaning1331 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1331 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1332 = true := by
  have hs : count1330 q = (countLit q [-40, -41, -42]) + (countLit q [-44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -42]) (l₂ := [-44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1320)) (literal (valuationOf q) (1326)) (literal (valuationOf q) (1332)) (countLit q [-40, -41, -42]) (countLit q [-44, -45, -48, -49]) (count1330 q) 2 1 (meaning1320 q) (meaning1326 q) (meaning1332 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1326 = false ∨ valuation q 1332 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1333 = true := by
  have hs : count1330 q = (countLit q [-40, -41, -42]) + (countLit q [-44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -42]) (l₂ := [-44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1320)) (literal (valuationOf q) (1327)) (literal (valuationOf q) (1333)) (countLit q [-40, -41, -42]) (countLit q [-44, -45, -48, -49]) (count1330 q) 2 2 (meaning1320 q) (meaning1327 q) (meaning1333 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1327 = false ∨ valuation q 1333 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1337 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_right (literal (valuationOf q) (1330)) (literal (valuationOf q) (1337)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 1 (meaning1330 q) (meaning1337 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1337 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1338 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_right (literal (valuationOf q) (1331)) (literal (valuationOf q) (1338)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 2 (meaning1331 q) (meaning1338 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1338 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1339 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_right (literal (valuationOf q) (1332)) (literal (valuationOf q) (1339)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 3 (meaning1332 q) (meaning1339 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1339 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1340 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_right (literal (valuationOf q) (1333)) (literal (valuationOf q) (1340)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 4 (meaning1333 q) (meaning1340 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1340 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1341 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_right (literal (valuationOf q) (1334)) (literal (valuationOf q) (1341)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 5 (meaning1334 q) (meaning1341 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1341 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1337 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_left (literal (valuationOf q) (1311)) (literal (valuationOf q) (1337)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 1 (meaning1311 q) (meaning1337 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1337 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1338 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1338)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 1 1 (meaning1311 q) (meaning1330 q) (meaning1338 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1330 = false ∨ valuation q 1338 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1339 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1331)) (literal (valuationOf q) (1339)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 1 2 (meaning1311 q) (meaning1331 q) (meaning1339 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1331 = false ∨ valuation q 1339 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1340 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1332)) (literal (valuationOf q) (1340)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 1 3 (meaning1311 q) (meaning1332 q) (meaning1340 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1332 = false ∨ valuation q 1340 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1341 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1333)) (literal (valuationOf q) (1341)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 1 4 (meaning1311 q) (meaning1333 q) (meaning1341 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1333 = false ∨ valuation q 1341 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1339 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1339)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 2 1 (meaning1312 q) (meaning1330 q) (meaning1339 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1330 = false ∨ valuation q 1339 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1340 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1331)) (literal (valuationOf q) (1340)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 2 2 (meaning1312 q) (meaning1331 q) (meaning1340 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1331 = false ∨ valuation q 1340 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E091.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112091
