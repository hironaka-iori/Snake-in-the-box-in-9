import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 903 = false ∨ valuationOf q 908 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (903)) (literal (valuationOf q) (908)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 1 1 (meaning895 q) (meaning903 q) (meaning908 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 903 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 903 = false ∨ valuation q 908 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 904 = false ∨ valuationOf q 909 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (904)) (literal (valuationOf q) (909)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 1 2 (meaning895 q) (meaning904 q) (meaning909 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 904 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 904 = false ∨ valuation q 909 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 905 = false ∨ valuationOf q 910 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (905)) (literal (valuationOf q) (910)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 1 3 (meaning895 q) (meaning905 q) (meaning910 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 905 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 905 = false ∨ valuation q 910 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 906 = false ∨ valuationOf q 911 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (906)) (literal (valuationOf q) (911)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 1 4 (meaning895 q) (meaning906 q) (meaning911 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 906 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 906 = false ∨ valuation q 911 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 908 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_left (literal (valuationOf q) (896)) (literal (valuationOf q) (908)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 2 (meaning896 q) (meaning908 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 908 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 903 = false ∨ valuationOf q 909 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (903)) (literal (valuationOf q) (909)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 2 1 (meaning896 q) (meaning903 q) (meaning909 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 903 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 903 = false ∨ valuation q 909 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 904 = false ∨ valuationOf q 910 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (904)) (literal (valuationOf q) (910)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 2 2 (meaning896 q) (meaning904 q) (meaning910 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 904 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 904 = false ∨ valuation q 910 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 905 = false ∨ valuationOf q 911 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (905)) (literal (valuationOf q) (911)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 2 3 (meaning896 q) (meaning905 q) (meaning911 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 905 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 905 = false ∨ valuation q 911 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 906 = false ∨ valuationOf q 912 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (906)) (literal (valuationOf q) (912)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 2 4 (meaning896 q) (meaning906 q) (meaning912 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 906 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 906 = false ∨ valuation q 912 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 909 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_left (literal (valuationOf q) (897)) (literal (valuationOf q) (909)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 3 (meaning897 q) (meaning909 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 909 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 903 = false ∨ valuationOf q 910 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (903)) (literal (valuationOf q) (910)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 3 1 (meaning897 q) (meaning903 q) (meaning910 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 903 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 903 = false ∨ valuation q 910 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 904 = false ∨ valuationOf q 911 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (904)) (literal (valuationOf q) (911)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 3 2 (meaning897 q) (meaning904 q) (meaning911 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 904 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 904 = false ∨ valuation q 911 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 905 = false ∨ valuationOf q 912 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (905)) (literal (valuationOf q) (912)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 3 3 (meaning897 q) (meaning905 q) (meaning912 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 905 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 905 = false ∨ valuation q 912 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 904 = false ∨ valuationOf q 912 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (904)) (literal (valuationOf q) (912)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 4 2 (meaning898 q) (meaning904 q) (meaning912 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 904 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 904 = false ∨ valuation q 912 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 919 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_right (literal (valuationOf q) (911)) (literal (valuationOf q) (919)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 5 (meaning911 q) (meaning919 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 919 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 907 = false ∨ valuationOf q 916 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (907)) (literal (valuationOf q) (916)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 1 1 (meaning883 q) (meaning907 q) (meaning916 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 907 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 907 = false ∨ valuation q 916 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 908 = false ∨ valuationOf q 917 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (908)) (literal (valuationOf q) (917)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 1 2 (meaning883 q) (meaning908 q) (meaning917 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 908 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 908 = false ∨ valuation q 917 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 909 = false ∨ valuationOf q 918 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (909)) (literal (valuationOf q) (918)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 1 3 (meaning883 q) (meaning909 q) (meaning918 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 909 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 909 = false ∨ valuation q 918 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 910 = false ∨ valuationOf q 919 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (910)) (literal (valuationOf q) (919)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 1 4 (meaning883 q) (meaning910 q) (meaning919 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 910 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 910 = false ∨ valuation q 919 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 911 = false ∨ valuationOf q 920 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (911)) (literal (valuationOf q) (920)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 1 5 (meaning883 q) (meaning911 q) (meaning920 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 911 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 911 = false ∨ valuation q 920 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 912 = false ∨ valuationOf q 921 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (912)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 1 6 (meaning883 q) (meaning912 q) (meaning921 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 912 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 912 = false ∨ valuation q 921 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 907 = false ∨ valuationOf q 917 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (907)) (literal (valuationOf q) (917)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 2 1 (meaning884 q) (meaning907 q) (meaning917 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 907 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 907 = false ∨ valuation q 917 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 908 = false ∨ valuationOf q 918 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (908)) (literal (valuationOf q) (918)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 2 2 (meaning884 q) (meaning908 q) (meaning918 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 908 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 908 = false ∨ valuation q 918 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 909 = false ∨ valuationOf q 919 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (909)) (literal (valuationOf q) (919)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 2 3 (meaning884 q) (meaning909 q) (meaning919 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 909 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 909 = false ∨ valuation q 919 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 910 = false ∨ valuationOf q 920 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (910)) (literal (valuationOf q) (920)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 2 4 (meaning884 q) (meaning910 q) (meaning920 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 910 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 910 = false ∨ valuation q 920 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 911 = false ∨ valuationOf q 921 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (911)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 2 5 (meaning884 q) (meaning911 q) (meaning921 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 911 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 911 = false ∨ valuation q 921 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 912 = false ∨ valuationOf q 922 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (912)) (literal (valuationOf q) (922)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 2 6 (meaning884 q) (meaning912 q) (meaning922 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 912 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 912 = false ∨ valuation q 922 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 917 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_left (literal (valuationOf q) (885)) (literal (valuationOf q) (917)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 3 (meaning885 q) (meaning917 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 917 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 907 = false ∨ valuationOf q 918 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (885)) (literal (valuationOf q) (907)) (literal (valuationOf q) (918)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 3 1 (meaning885 q) (meaning907 q) (meaning918 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 907 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 907 = false ∨ valuation q 918 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 908 = false ∨ valuationOf q 919 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (885)) (literal (valuationOf q) (908)) (literal (valuationOf q) (919)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 3 2 (meaning885 q) (meaning908 q) (meaning919 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 908 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 908 = false ∨ valuation q 919 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 909 = false ∨ valuationOf q 920 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (885)) (literal (valuationOf q) (909)) (literal (valuationOf q) (920)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 3 3 (meaning885 q) (meaning909 q) (meaning920 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 909 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 909 = false ∨ valuation q 920 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 910 = false ∨ valuationOf q 921 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (885)) (literal (valuationOf q) (910)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 3 4 (meaning885 q) (meaning910 q) (meaning921 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 910 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 910 = false ∨ valuation q 921 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E057.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112057
