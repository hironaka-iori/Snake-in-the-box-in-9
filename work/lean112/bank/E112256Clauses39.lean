import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 915 = false ∨ valuationOf q 917 = true := by
  have hs : count917 q = (countLit q [-41, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-43, -44])
  have hm := merge_right (literal (valuationOf q) (915)) (literal (valuationOf q) (917)) (countLit q [-41, -42]) (countLit q [-43, -44]) (count917 q) 1 (meaning915 q) (meaning917 q) hs
  change valuationOf q 915 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 915 = false ∨ valuation q 917 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 918 = true := by
  have hs : count917 q = (countLit q [-41, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-43, -44])
  have hm := merge_right (literal (valuationOf q) (916)) (literal (valuationOf q) (918)) (countLit q [-41, -42]) (countLit q [-43, -44]) (count917 q) 2 (meaning916 q) (meaning918 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 918 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 913 = false ∨ valuationOf q 917 = true := by
  have hs : count917 q = (countLit q [-41, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-43, -44])
  have hm := merge_left (literal (valuationOf q) (913)) (literal (valuationOf q) (917)) (countLit q [-41, -42]) (countLit q [-43, -44]) (count917 q) 1 (meaning913 q) (meaning917 q) hs
  change valuationOf q 913 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 913 = false ∨ valuation q 917 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 913 = false ∨ valuationOf q 915 = false ∨ valuationOf q 918 = true := by
  have hs : count917 q = (countLit q [-41, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (913)) (literal (valuationOf q) (915)) (literal (valuationOf q) (918)) (countLit q [-41, -42]) (countLit q [-43, -44]) (count917 q) 1 1 (meaning913 q) (meaning915 q) (meaning918 q) hs
  change valuationOf q 913 = false ∨ valuationOf q 915 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 913 = false ∨ valuation q 915 = false ∨ valuation q 918 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 913 = false ∨ valuationOf q 916 = false ∨ valuationOf q 919 = true := by
  have hs : count917 q = (countLit q [-41, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (913)) (literal (valuationOf q) (916)) (literal (valuationOf q) (919)) (countLit q [-41, -42]) (countLit q [-43, -44]) (count917 q) 1 2 (meaning913 q) (meaning916 q) (meaning919 q) hs
  change valuationOf q 913 = false ∨ valuationOf q 916 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 913 = false ∨ valuation q 916 = false ∨ valuation q 919 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 918 = true := by
  have hs : count917 q = (countLit q [-41, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-43, -44])
  have hm := merge_left (literal (valuationOf q) (914)) (literal (valuationOf q) (918)) (countLit q [-41, -42]) (countLit q [-43, -44]) (count917 q) 2 (meaning914 q) (meaning918 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 918 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 915 = false ∨ valuationOf q 919 = true := by
  have hs : count917 q = (countLit q [-41, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (914)) (literal (valuationOf q) (915)) (literal (valuationOf q) (919)) (countLit q [-41, -42]) (countLit q [-43, -44]) (count917 q) 2 1 (meaning914 q) (meaning915 q) (meaning919 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 915 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 915 = false ∨ valuation q 919 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 916 = false ∨ valuationOf q 920 = true := by
  have hs : count917 q = (countLit q [-41, -42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (914)) (literal (valuationOf q) (916)) (literal (valuationOf q) (920)) (countLit q [-41, -42]) (countLit q [-43, -44]) (count917 q) 2 2 (meaning914 q) (meaning916 q) (meaning920 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 916 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 916 = false ∨ valuation q 920 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 921 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_right (literal (valuationOf q) (917)) (literal (valuationOf q) (921)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 1 (meaning917 q) (meaning921 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 921 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 922 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_right (literal (valuationOf q) (918)) (literal (valuationOf q) (922)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 2 (meaning918 q) (meaning922 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 922 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 923 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_right (literal (valuationOf q) (919)) (literal (valuationOf q) (923)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 3 (meaning919 q) (meaning923 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 923 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 924 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_right (literal (valuationOf q) (920)) (literal (valuationOf q) (924)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 4 (meaning920 q) (meaning924 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 924 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 921 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_left (literal (valuationOf q) (910)) (literal (valuationOf q) (921)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 1 (meaning910 q) (meaning921 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 921 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 917 = false ∨ valuationOf q 922 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (917)) (literal (valuationOf q) (922)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 1 1 (meaning910 q) (meaning917 q) (meaning922 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 917 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 917 = false ∨ valuation q 922 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 918 = false ∨ valuationOf q 923 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (918)) (literal (valuationOf q) (923)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 1 2 (meaning910 q) (meaning918 q) (meaning923 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 918 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 918 = false ∨ valuation q 923 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 919 = false ∨ valuationOf q 924 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (919)) (literal (valuationOf q) (924)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 1 3 (meaning910 q) (meaning919 q) (meaning924 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 919 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 919 = false ∨ valuation q 924 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 920 = false ∨ valuationOf q 925 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (920)) (literal (valuationOf q) (925)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 1 4 (meaning910 q) (meaning920 q) (meaning925 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 920 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 920 = false ∨ valuation q 925 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 922 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_left (literal (valuationOf q) (911)) (literal (valuationOf q) (922)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 2 (meaning911 q) (meaning922 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 922 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 917 = false ∨ valuationOf q 923 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (911)) (literal (valuationOf q) (917)) (literal (valuationOf q) (923)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 2 1 (meaning911 q) (meaning917 q) (meaning923 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 917 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 917 = false ∨ valuation q 923 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 918 = false ∨ valuationOf q 924 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (911)) (literal (valuationOf q) (918)) (literal (valuationOf q) (924)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 2 2 (meaning911 q) (meaning918 q) (meaning924 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 918 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 918 = false ∨ valuation q 924 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 919 = false ∨ valuationOf q 925 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (911)) (literal (valuationOf q) (919)) (literal (valuationOf q) (925)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 2 3 (meaning911 q) (meaning919 q) (meaning925 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 919 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 919 = false ∨ valuation q 925 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 920 = false ∨ valuationOf q 926 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (911)) (literal (valuationOf q) (920)) (literal (valuationOf q) (926)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 2 4 (meaning911 q) (meaning920 q) (meaning926 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 920 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 920 = false ∨ valuation q 926 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 923 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_left (literal (valuationOf q) (912)) (literal (valuationOf q) (923)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 3 (meaning912 q) (meaning923 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 923 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 917 = false ∨ valuationOf q 924 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (912)) (literal (valuationOf q) (917)) (literal (valuationOf q) (924)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 3 1 (meaning912 q) (meaning917 q) (meaning924 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 917 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 917 = false ∨ valuation q 924 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 918 = false ∨ valuationOf q 925 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (912)) (literal (valuationOf q) (918)) (literal (valuationOf q) (925)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 3 2 (meaning912 q) (meaning918 q) (meaning925 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 918 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 918 = false ∨ valuation q 925 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 919 = false ∨ valuationOf q 926 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (912)) (literal (valuationOf q) (919)) (literal (valuationOf q) (926)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 3 3 (meaning912 q) (meaning919 q) (meaning926 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 919 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 919 = false ∨ valuation q 926 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 920 = false ∨ valuationOf q 927 = true := by
  have hs : count921 q = (countLit q [-33, -34, -36]) + (countLit q [-41, -42, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-41, -42, -43, -44])
  have hm := merge_two (literal (valuationOf q) (912)) (literal (valuationOf q) (920)) (literal (valuationOf q) (927)) (countLit q [-33, -34, -36]) (countLit q [-41, -42, -43, -44]) (count921 q) 3 4 (meaning912 q) (meaning920 q) (meaning927 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 920 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 920 = false ∨ valuation q 927 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 928 = true := by
  have hs : count928 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (928)) (countLit q [-45]) (countLit q [-47]) (count928 q) 1 (meaningNeg47 q) (meaning928 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 928 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 928 = true := by
  have hs : count928 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (928)) (countLit q [-45]) (countLit q [-47]) (count928 q) 1 (meaningNeg45 q) (meaning928 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 928 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 47 = true ∨ valuationOf q 929 = true := by
  have hs : count928 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (929)) (countLit q [-45]) (countLit q [-47]) (count928 q) 1 1 (meaningNeg45 q) (meaningNeg47 q) (meaning929 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 47 = true ∨ valuation q 929 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 930 = true := by
  have hs : count930 q = (countLit q [-49]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (930)) (countLit q [-49]) (countLit q [-53]) (count930 q) 1 (meaningNeg53 q) (meaning930 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 930 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 930 = true := by
  have hs : count930 q = (countLit q [-49]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (930)) (countLit q [-49]) (countLit q [-53]) (count930 q) 1 (meaningNeg49 q) (meaning930 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 930 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E256.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112256
