import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 911 = false ∨ valuationOf q 922 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (885)) (literal (valuationOf q) (911)) (literal (valuationOf q) (922)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 3 5 (meaning885 q) (meaning911 q) (meaning922 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 911 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 911 = false ∨ valuation q 922 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 912 = false ∨ valuationOf q 923 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (885)) (literal (valuationOf q) (912)) (literal (valuationOf q) (923)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 3 6 (meaning885 q) (meaning912 q) (meaning923 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 912 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 912 = false ∨ valuation q 923 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 886 = false ∨ valuationOf q 907 = false ∨ valuationOf q 919 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (886)) (literal (valuationOf q) (907)) (literal (valuationOf q) (919)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 4 1 (meaning886 q) (meaning907 q) (meaning919 q) hs
  change valuationOf q 886 = false ∨ valuationOf q 907 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 886 = false ∨ valuation q 907 = false ∨ valuation q 919 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 886 = false ∨ valuationOf q 908 = false ∨ valuationOf q 920 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (886)) (literal (valuationOf q) (908)) (literal (valuationOf q) (920)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 4 2 (meaning886 q) (meaning908 q) (meaning920 q) hs
  change valuationOf q 886 = false ∨ valuationOf q 908 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 886 = false ∨ valuation q 908 = false ∨ valuation q 920 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 886 = false ∨ valuationOf q 909 = false ∨ valuationOf q 921 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (886)) (literal (valuationOf q) (909)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 4 3 (meaning886 q) (meaning909 q) (meaning921 q) hs
  change valuationOf q 886 = false ∨ valuationOf q 909 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 886 = false ∨ valuation q 909 = false ∨ valuation q 921 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 886 = false ∨ valuationOf q 910 = false ∨ valuationOf q 922 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (886)) (literal (valuationOf q) (910)) (literal (valuationOf q) (922)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 4 4 (meaning886 q) (meaning910 q) (meaning922 q) hs
  change valuationOf q 886 = false ∨ valuationOf q 910 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 886 = false ∨ valuation q 910 = false ∨ valuation q 922 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 907 = false ∨ valuationOf q 920 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (887)) (literal (valuationOf q) (907)) (literal (valuationOf q) (920)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 5 1 (meaning887 q) (meaning907 q) (meaning920 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 907 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 907 = false ∨ valuation q 920 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 908 = false ∨ valuationOf q 921 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (887)) (literal (valuationOf q) (908)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 5 2 (meaning887 q) (meaning908 q) (meaning921 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 908 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 908 = false ∨ valuation q 921 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 909 = false ∨ valuationOf q 922 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (887)) (literal (valuationOf q) (909)) (literal (valuationOf q) (922)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 5 3 (meaning887 q) (meaning909 q) (meaning922 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 909 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 909 = false ∨ valuation q 922 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 910 = false ∨ valuationOf q 923 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (887)) (literal (valuationOf q) (910)) (literal (valuationOf q) (923)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 5 4 (meaning887 q) (meaning910 q) (meaning923 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 910 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 910 = false ∨ valuation q 923 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 888 = false ∨ valuationOf q 907 = false ∨ valuationOf q 921 = true := by
  have hs : count915 q = (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) + (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7, -9, -10, -11, -15]) (l₂ := [-17, -19, -22, -25, -26, -28, -30, -33])
  have hm := merge_two (literal (valuationOf q) (888)) (literal (valuationOf q) (907)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -6, -7, -9, -10, -11, -15]) (countLit q [-17, -19, -22, -25, -26, -28, -30, -33]) (count915 q) 6 1 (meaning888 q) (meaning907 q) (meaning921 q) hs
  change valuationOf q 888 = false ∨ valuationOf q 907 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 888 = false ∨ valuation q 907 = false ∨ valuation q 921 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 931 = true := by
  have hs : count931 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (931)) (countLit q [-35]) (countLit q [-36]) (count931 q) 1 (meaningNeg36 q) (meaning931 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 931 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 931 = true := by
  have hs : count931 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (931)) (countLit q [-35]) (countLit q [-36]) (count931 q) 1 (meaningNeg35 q) (meaning931 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 931 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 36 = true ∨ valuationOf q 932 = true := by
  have hs : count931 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (932)) (countLit q [-35]) (countLit q [-36]) (count931 q) 1 1 (meaningNeg35 q) (meaningNeg36 q) (meaning932 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 36 = true ∨ valuation q 932 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 933 = true := by
  have hs : count933 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (933)) (countLit q [-39]) (countLit q [-42]) (count933 q) 1 (meaningNeg42 q) (meaning933 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 933 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 933 = true := by
  have hs : count933 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (933)) (countLit q [-39]) (countLit q [-42]) (count933 q) 1 (meaningNeg39 q) (meaning933 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 933 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 42 = true ∨ valuationOf q 934 = true := by
  have hs : count933 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (934)) (countLit q [-39]) (countLit q [-42]) (count933 q) 1 1 (meaningNeg39 q) (meaningNeg42 q) (meaning934 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 42 = true ∨ valuation q 934 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 935 = true := by
  have hs : count935 q = (countLit q [-35, -36]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -42])
  have hm := merge_right (literal (valuationOf q) (933)) (literal (valuationOf q) (935)) (countLit q [-35, -36]) (countLit q [-39, -42]) (count935 q) 1 (meaning933 q) (meaning935 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 935 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 936 = true := by
  have hs : count935 q = (countLit q [-35, -36]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -42])
  have hm := merge_right (literal (valuationOf q) (934)) (literal (valuationOf q) (936)) (countLit q [-35, -36]) (countLit q [-39, -42]) (count935 q) 2 (meaning934 q) (meaning936 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 936 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 935 = true := by
  have hs : count935 q = (countLit q [-35, -36]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -42])
  have hm := merge_left (literal (valuationOf q) (931)) (literal (valuationOf q) (935)) (countLit q [-35, -36]) (countLit q [-39, -42]) (count935 q) 1 (meaning931 q) (meaning935 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 935 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 933 = false ∨ valuationOf q 936 = true := by
  have hs : count935 q = (countLit q [-35, -36]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -42])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (933)) (literal (valuationOf q) (936)) (countLit q [-35, -36]) (countLit q [-39, -42]) (count935 q) 1 1 (meaning931 q) (meaning933 q) (meaning936 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 933 = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 933 = false ∨ valuation q 936 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 934 = false ∨ valuationOf q 937 = true := by
  have hs : count935 q = (countLit q [-35, -36]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -42])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (934)) (literal (valuationOf q) (937)) (countLit q [-35, -36]) (countLit q [-39, -42]) (count935 q) 1 2 (meaning931 q) (meaning934 q) (meaning937 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 934 = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 934 = false ∨ valuation q 937 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 936 = true := by
  have hs : count935 q = (countLit q [-35, -36]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -42])
  have hm := merge_left (literal (valuationOf q) (932)) (literal (valuationOf q) (936)) (countLit q [-35, -36]) (countLit q [-39, -42]) (count935 q) 2 (meaning932 q) (meaning936 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 936 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 933 = false ∨ valuationOf q 937 = true := by
  have hs : count935 q = (countLit q [-35, -36]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -42])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (933)) (literal (valuationOf q) (937)) (countLit q [-35, -36]) (countLit q [-39, -42]) (count935 q) 2 1 (meaning932 q) (meaning933 q) (meaning937 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 933 = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 933 = false ∨ valuation q 937 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 934 = false ∨ valuationOf q 938 = true := by
  have hs : count935 q = (countLit q [-35, -36]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -42])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (934)) (literal (valuationOf q) (938)) (countLit q [-35, -36]) (countLit q [-39, -42]) (count935 q) 2 2 (meaning932 q) (meaning934 q) (meaning938 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 934 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 934 = false ∨ valuation q 938 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 939 = true := by
  have hs : count939 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (939)) (countLit q [-43]) (countLit q [-46]) (count939 q) 1 (meaningNeg46 q) (meaning939 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 939 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 939 = true := by
  have hs : count939 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (939)) (countLit q [-43]) (countLit q [-46]) (count939 q) 1 (meaningNeg43 q) (meaning939 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 939 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 46 = true ∨ valuationOf q 940 = true := by
  have hs : count939 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (940)) (countLit q [-43]) (countLit q [-46]) (count939 q) 1 1 (meaningNeg43 q) (meaningNeg46 q) (meaning940 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 46 = true ∨ valuation q 940 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 941 = true := by
  have hs : count941 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (941)) (countLit q [-47]) (countLit q [-48]) (count941 q) 1 (meaningNeg48 q) (meaning941 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 941 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 941 = true := by
  have hs : count941 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (941)) (countLit q [-47]) (countLit q [-48]) (count941 q) 1 (meaningNeg47 q) (meaning941 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 941 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 48 = true ∨ valuationOf q 942 = true := by
  have hs : count941 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (942)) (countLit q [-47]) (countLit q [-48]) (count941 q) 1 1 (meaningNeg47 q) (meaningNeg48 q) (meaning942 q) hs
  change (! (valuationOf q 47)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 48 = true ∨ valuation q 942 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 941 = false ∨ valuationOf q 943 = true := by
  have hs : count943 q = (countLit q [-43, -46]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-47, -48])
  have hm := merge_right (literal (valuationOf q) (941)) (literal (valuationOf q) (943)) (countLit q [-43, -46]) (countLit q [-47, -48]) (count943 q) 1 (meaning941 q) (meaning943 q) hs
  change valuationOf q 941 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 941 = false ∨ valuation q 943 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E057.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112057
