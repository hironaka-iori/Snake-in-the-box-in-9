import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 877 = true := by
  have hs : count877 q = (countLit q [-11]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-15])
  have hm := merge_right (literal (valuationOf q) (-15)) (literal (valuationOf q) (877)) (countLit q [-11]) (countLit q [-15]) (count877 q) 1 (meaningNeg15 q) (meaning877 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 877 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 877 = true := by
  have hs : count877 q = (countLit q [-11]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-15])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (877)) (countLit q [-11]) (countLit q [-15]) (count877 q) 1 (meaningNeg11 q) (meaning877 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 877 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 15 = true ∨ valuationOf q 878 = true := by
  have hs : count877 q = (countLit q [-11]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (878)) (countLit q [-11]) (countLit q [-15]) (count877 q) 1 1 (meaningNeg11 q) (meaningNeg15 q) (meaning878 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 15 = true ∨ valuation q 878 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-9, -10]) + (countLit q [-11, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -15])
  have hm := merge_right (literal (valuationOf q) (877)) (literal (valuationOf q) (879)) (countLit q [-9, -10]) (countLit q [-11, -15]) (count879 q) 1 (meaning877 q) (meaning879 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 879 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-9, -10]) + (countLit q [-11, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -15])
  have hm := merge_right (literal (valuationOf q) (878)) (literal (valuationOf q) (880)) (countLit q [-9, -10]) (countLit q [-11, -15]) (count879 q) 2 (meaning878 q) (meaning880 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 880 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-9, -10]) + (countLit q [-11, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -15])
  have hm := merge_left (literal (valuationOf q) (875)) (literal (valuationOf q) (879)) (countLit q [-9, -10]) (countLit q [-11, -15]) (count879 q) 1 (meaning875 q) (meaning879 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 879 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 877 = false ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-9, -10]) + (countLit q [-11, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -15])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (877)) (literal (valuationOf q) (880)) (countLit q [-9, -10]) (countLit q [-11, -15]) (count879 q) 1 1 (meaning875 q) (meaning877 q) (meaning880 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 877 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 877 = false ∨ valuation q 880 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 878 = false ∨ valuationOf q 881 = true := by
  have hs : count879 q = (countLit q [-9, -10]) + (countLit q [-11, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -15])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (878)) (literal (valuationOf q) (881)) (countLit q [-9, -10]) (countLit q [-11, -15]) (count879 q) 1 2 (meaning875 q) (meaning878 q) (meaning881 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 878 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 878 = false ∨ valuation q 881 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-9, -10]) + (countLit q [-11, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -15])
  have hm := merge_left (literal (valuationOf q) (876)) (literal (valuationOf q) (880)) (countLit q [-9, -10]) (countLit q [-11, -15]) (count879 q) 2 (meaning876 q) (meaning880 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 880 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 877 = false ∨ valuationOf q 881 = true := by
  have hs : count879 q = (countLit q [-9, -10]) + (countLit q [-11, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -15])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (877)) (literal (valuationOf q) (881)) (countLit q [-9, -10]) (countLit q [-11, -15]) (count879 q) 2 1 (meaning876 q) (meaning877 q) (meaning881 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 877 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 877 = false ∨ valuation q 881 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 878 = false ∨ valuationOf q 882 = true := by
  have hs : count879 q = (countLit q [-9, -10]) + (countLit q [-11, -15]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -15])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (878)) (literal (valuationOf q) (882)) (countLit q [-9, -10]) (countLit q [-11, -15]) (count879 q) 2 2 (meaning876 q) (meaning878 q) (meaning882 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 878 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 878 = false ∨ valuation q 882 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_right (literal (valuationOf q) (879)) (literal (valuationOf q) (883)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 1 (meaning879 q) (meaning883 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 883 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_right (literal (valuationOf q) (880)) (literal (valuationOf q) (884)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 2 (meaning880 q) (meaning884 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 884 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 885 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_right (literal (valuationOf q) (881)) (literal (valuationOf q) (885)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 3 (meaning881 q) (meaning885 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 885 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 886 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_right (literal (valuationOf q) (882)) (literal (valuationOf q) (886)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 4 (meaning882 q) (meaning886 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 886 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_left (literal (valuationOf q) (871)) (literal (valuationOf q) (883)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 1 (meaning871 q) (meaning883 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 883 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 879 = false ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (879)) (literal (valuationOf q) (884)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 1 1 (meaning871 q) (meaning879 q) (meaning884 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 879 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 879 = false ∨ valuation q 884 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 880 = false ∨ valuationOf q 885 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (880)) (literal (valuationOf q) (885)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 1 2 (meaning871 q) (meaning880 q) (meaning885 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 880 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 880 = false ∨ valuation q 885 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 881 = false ∨ valuationOf q 886 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (881)) (literal (valuationOf q) (886)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 1 3 (meaning871 q) (meaning881 q) (meaning886 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 881 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 881 = false ∨ valuation q 886 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 882 = false ∨ valuationOf q 887 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (882)) (literal (valuationOf q) (887)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 1 4 (meaning871 q) (meaning882 q) (meaning887 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 882 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 882 = false ∨ valuation q 887 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_left (literal (valuationOf q) (872)) (literal (valuationOf q) (884)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 2 (meaning872 q) (meaning884 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 884 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 879 = false ∨ valuationOf q 885 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (879)) (literal (valuationOf q) (885)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 2 1 (meaning872 q) (meaning879 q) (meaning885 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 879 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 879 = false ∨ valuation q 885 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 880 = false ∨ valuationOf q 886 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (880)) (literal (valuationOf q) (886)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 2 2 (meaning872 q) (meaning880 q) (meaning886 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 880 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 880 = false ∨ valuation q 886 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 881 = false ∨ valuationOf q 887 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (881)) (literal (valuationOf q) (887)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 2 3 (meaning872 q) (meaning881 q) (meaning887 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 881 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 881 = false ∨ valuation q 887 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 885 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_left (literal (valuationOf q) (873)) (literal (valuationOf q) (885)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 3 (meaning873 q) (meaning885 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 885 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 879 = false ∨ valuationOf q 886 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (873)) (literal (valuationOf q) (879)) (literal (valuationOf q) (886)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 3 1 (meaning873 q) (meaning879 q) (meaning886 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 879 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 879 = false ∨ valuation q 886 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 880 = false ∨ valuationOf q 887 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (873)) (literal (valuationOf q) (880)) (literal (valuationOf q) (887)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 3 2 (meaning873 q) (meaning880 q) (meaning887 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 880 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 880 = false ∨ valuation q 887 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 881 = false ∨ valuationOf q 888 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (873)) (literal (valuationOf q) (881)) (literal (valuationOf q) (888)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 3 3 (meaning873 q) (meaning881 q) (meaning888 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 881 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 881 = false ∨ valuation q 888 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 886 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_left (literal (valuationOf q) (874)) (literal (valuationOf q) (886)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 4 (meaning874 q) (meaning886 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 886 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 879 = false ∨ valuationOf q 887 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (874)) (literal (valuationOf q) (879)) (literal (valuationOf q) (887)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 4 1 (meaning874 q) (meaning879 q) (meaning887 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 879 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 879 = false ∨ valuation q 887 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 880 = false ∨ valuationOf q 888 = true := by
  have hs : count883 q = (countLit q [-1, -4, -6, -7]) + (countLit q [-9, -10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -6, -7]) (l₂ := [-9, -10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (874)) (literal (valuationOf q) (880)) (literal (valuationOf q) (888)) (countLit q [-1, -4, -6, -7]) (countLit q [-9, -10, -11, -15]) (count883 q) 4 2 (meaning874 q) (meaning880 q) (meaning888 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 880 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 880 = false ∨ valuation q 888 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 891 = true := by
  have hs : count891 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (891)) (countLit q [-17]) (countLit q [-19]) (count891 q) 1 (meaningNeg19 q) (meaning891 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 891 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E057.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112057
