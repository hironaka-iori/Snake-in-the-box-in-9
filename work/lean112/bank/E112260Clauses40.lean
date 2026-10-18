import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 910 = true := by
  have hs : count910 q = (countLit q [-32]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (908)) (literal (valuationOf q) (910)) (countLit q [-32]) (countLit q [-34, -36]) (count910 q) 1 (meaning908 q) (meaning910 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 910 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 911 = true := by
  have hs : count910 q = (countLit q [-32]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (909)) (literal (valuationOf q) (911)) (countLit q [-32]) (countLit q [-34, -36]) (count910 q) 2 (meaning909 q) (meaning911 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 911 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 910 = true := by
  have hs : count910 q = (countLit q [-32]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -36])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (910)) (countLit q [-32]) (countLit q [-34, -36]) (count910 q) 1 (meaningNeg32 q) (meaning910 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 910 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 908 = false ∨ valuationOf q 911 = true := by
  have hs : count910 q = (countLit q [-32]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (908)) (literal (valuationOf q) (911)) (countLit q [-32]) (countLit q [-34, -36]) (count910 q) 1 1 (meaningNeg32 q) (meaning908 q) (meaning911 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 908 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 908 = false ∨ valuation q 911 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 909 = false ∨ valuationOf q 912 = true := by
  have hs : count910 q = (countLit q [-32]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (909)) (literal (valuationOf q) (912)) (countLit q [-32]) (countLit q [-34, -36]) (count910 q) 1 2 (meaningNeg32 q) (meaning909 q) (meaning912 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 909 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 909 = false ∨ valuation q 912 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 913 = true := by
  have hs : count913 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (913)) (countLit q [-40]) (countLit q [-42]) (count913 q) 1 (meaningNeg42 q) (meaning913 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 913 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 913 = true := by
  have hs : count913 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (913)) (countLit q [-40]) (countLit q [-42]) (count913 q) 1 (meaningNeg40 q) (meaning913 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 913 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 42 = true ∨ valuationOf q 914 = true := by
  have hs : count913 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (914)) (countLit q [-40]) (countLit q [-42]) (count913 q) 1 1 (meaningNeg40 q) (meaningNeg42 q) (meaning914 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 914 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 914 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 915 = true := by
  have hs : count915 q = (countLit q [-44]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (915)) (countLit q [-44]) (countLit q [-46]) (count915 q) 1 (meaningNeg46 q) (meaning915 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 915 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 915 = true := by
  have hs : count915 q = (countLit q [-44]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (915)) (countLit q [-44]) (countLit q [-46]) (count915 q) 1 (meaningNeg44 q) (meaning915 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 915 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 46 = true ∨ valuationOf q 916 = true := by
  have hs : count915 q = (countLit q [-44]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (916)) (countLit q [-44]) (countLit q [-46]) (count915 q) 1 1 (meaningNeg44 q) (meaningNeg46 q) (meaning916 q) hs
  change (! (valuationOf q 44)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 46 = true ∨ valuation q 916 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 915 = false ∨ valuationOf q 917 = true := by
  have hs : count917 q = (countLit q [-40, -42]) + (countLit q [-44, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -46])
  have hm := merge_right (literal (valuationOf q) (915)) (literal (valuationOf q) (917)) (countLit q [-40, -42]) (countLit q [-44, -46]) (count917 q) 1 (meaning915 q) (meaning917 q) hs
  change valuationOf q 915 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 915 = false ∨ valuation q 917 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 918 = true := by
  have hs : count917 q = (countLit q [-40, -42]) + (countLit q [-44, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -46])
  have hm := merge_right (literal (valuationOf q) (916)) (literal (valuationOf q) (918)) (countLit q [-40, -42]) (countLit q [-44, -46]) (count917 q) 2 (meaning916 q) (meaning918 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 918 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 913 = false ∨ valuationOf q 917 = true := by
  have hs : count917 q = (countLit q [-40, -42]) + (countLit q [-44, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -46])
  have hm := merge_left (literal (valuationOf q) (913)) (literal (valuationOf q) (917)) (countLit q [-40, -42]) (countLit q [-44, -46]) (count917 q) 1 (meaning913 q) (meaning917 q) hs
  change valuationOf q 913 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 913 = false ∨ valuation q 917 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 913 = false ∨ valuationOf q 915 = false ∨ valuationOf q 918 = true := by
  have hs : count917 q = (countLit q [-40, -42]) + (countLit q [-44, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -46])
  have hm := merge_two (literal (valuationOf q) (913)) (literal (valuationOf q) (915)) (literal (valuationOf q) (918)) (countLit q [-40, -42]) (countLit q [-44, -46]) (count917 q) 1 1 (meaning913 q) (meaning915 q) (meaning918 q) hs
  change valuationOf q 913 = false ∨ valuationOf q 915 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 913 = false ∨ valuation q 915 = false ∨ valuation q 918 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 913 = false ∨ valuationOf q 916 = false ∨ valuationOf q 919 = true := by
  have hs : count917 q = (countLit q [-40, -42]) + (countLit q [-44, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -46])
  have hm := merge_two (literal (valuationOf q) (913)) (literal (valuationOf q) (916)) (literal (valuationOf q) (919)) (countLit q [-40, -42]) (countLit q [-44, -46]) (count917 q) 1 2 (meaning913 q) (meaning916 q) (meaning919 q) hs
  change valuationOf q 913 = false ∨ valuationOf q 916 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 913 = false ∨ valuation q 916 = false ∨ valuation q 919 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 918 = true := by
  have hs : count917 q = (countLit q [-40, -42]) + (countLit q [-44, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -46])
  have hm := merge_left (literal (valuationOf q) (914)) (literal (valuationOf q) (918)) (countLit q [-40, -42]) (countLit q [-44, -46]) (count917 q) 2 (meaning914 q) (meaning918 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 918 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 915 = false ∨ valuationOf q 919 = true := by
  have hs : count917 q = (countLit q [-40, -42]) + (countLit q [-44, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -46])
  have hm := merge_two (literal (valuationOf q) (914)) (literal (valuationOf q) (915)) (literal (valuationOf q) (919)) (countLit q [-40, -42]) (countLit q [-44, -46]) (count917 q) 2 1 (meaning914 q) (meaning915 q) (meaning919 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 915 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 915 = false ∨ valuation q 919 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 916 = false ∨ valuationOf q 920 = true := by
  have hs : count917 q = (countLit q [-40, -42]) + (countLit q [-44, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -46])
  have hm := merge_two (literal (valuationOf q) (914)) (literal (valuationOf q) (916)) (literal (valuationOf q) (920)) (countLit q [-40, -42]) (countLit q [-44, -46]) (count917 q) 2 2 (meaning914 q) (meaning916 q) (meaning920 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 916 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 916 = false ∨ valuation q 920 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 921 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_right (literal (valuationOf q) (917)) (literal (valuationOf q) (921)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 1 (meaning917 q) (meaning921 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 921 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 922 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_right (literal (valuationOf q) (918)) (literal (valuationOf q) (922)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 2 (meaning918 q) (meaning922 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 922 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 923 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_right (literal (valuationOf q) (919)) (literal (valuationOf q) (923)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 3 (meaning919 q) (meaning923 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 923 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 924 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_right (literal (valuationOf q) (920)) (literal (valuationOf q) (924)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 4 (meaning920 q) (meaning924 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 924 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 921 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_left (literal (valuationOf q) (910)) (literal (valuationOf q) (921)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 1 (meaning910 q) (meaning921 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 921 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 917 = false ∨ valuationOf q 922 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (917)) (literal (valuationOf q) (922)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 1 1 (meaning910 q) (meaning917 q) (meaning922 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 917 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 917 = false ∨ valuation q 922 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 918 = false ∨ valuationOf q 923 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (918)) (literal (valuationOf q) (923)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 1 2 (meaning910 q) (meaning918 q) (meaning923 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 918 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 918 = false ∨ valuation q 923 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 919 = false ∨ valuationOf q 924 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (919)) (literal (valuationOf q) (924)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 1 3 (meaning910 q) (meaning919 q) (meaning924 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 919 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 919 = false ∨ valuation q 924 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 920 = false ∨ valuationOf q 925 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (920)) (literal (valuationOf q) (925)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 1 4 (meaning910 q) (meaning920 q) (meaning925 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 920 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 920 = false ∨ valuation q 925 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 922 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_left (literal (valuationOf q) (911)) (literal (valuationOf q) (922)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 2 (meaning911 q) (meaning922 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 922 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 917 = false ∨ valuationOf q 923 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_two (literal (valuationOf q) (911)) (literal (valuationOf q) (917)) (literal (valuationOf q) (923)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 2 1 (meaning911 q) (meaning917 q) (meaning923 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 917 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 917 = false ∨ valuation q 923 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 918 = false ∨ valuationOf q 924 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_two (literal (valuationOf q) (911)) (literal (valuationOf q) (918)) (literal (valuationOf q) (924)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 2 2 (meaning911 q) (meaning918 q) (meaning924 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 918 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 918 = false ∨ valuation q 924 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 919 = false ∨ valuationOf q 925 = true := by
  have hs : count921 q = (countLit q [-32, -34, -36]) + (countLit q [-40, -42, -44, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-40, -42, -44, -46])
  have hm := merge_two (literal (valuationOf q) (911)) (literal (valuationOf q) (919)) (literal (valuationOf q) (925)) (countLit q [-32, -34, -36]) (countLit q [-40, -42, -44, -46]) (count921 q) 2 3 (meaning911 q) (meaning919 q) (meaning925 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 919 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 919 = false ∨ valuation q 925 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E260.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112260
