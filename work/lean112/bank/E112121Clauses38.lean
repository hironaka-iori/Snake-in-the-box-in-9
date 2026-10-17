import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 905 = false ∨ valuationOf q 918 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (905)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 5 3 (meaning883 q) (meaning905 q) (meaning918 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 905 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 905 = false ∨ valuation q 918 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 906 = false ∨ valuationOf q 919 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (906)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 5 4 (meaning883 q) (meaning906 q) (meaning919 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 906 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 906 = false ∨ valuation q 919 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 907 = false ∨ valuationOf q 920 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (907)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 5 5 (meaning883 q) (meaning907 q) (meaning920 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 907 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 907 = false ∨ valuation q 920 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 908 = false ∨ valuationOf q 921 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (908)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 5 6 (meaning883 q) (meaning908 q) (meaning921 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 908 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 908 = false ∨ valuation q 921 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 909 = false ∨ valuationOf q 922 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (909)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 5 7 (meaning883 q) (meaning909 q) (meaning922 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 909 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 909 = false ∨ valuation q 922 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 903 = false ∨ valuationOf q 917 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (903)) (literal (valuationOf q) (917)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 6 1 (meaning884 q) (meaning903 q) (meaning917 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 903 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 903 = false ∨ valuation q 917 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 904 = false ∨ valuationOf q 918 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (904)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 6 2 (meaning884 q) (meaning904 q) (meaning918 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 904 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 904 = false ∨ valuation q 918 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 905 = false ∨ valuationOf q 919 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (905)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 6 3 (meaning884 q) (meaning905 q) (meaning919 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 905 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 905 = false ∨ valuation q 919 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 906 = false ∨ valuationOf q 920 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (906)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 6 4 (meaning884 q) (meaning906 q) (meaning920 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 906 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 906 = false ∨ valuation q 920 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 907 = false ∨ valuationOf q 921 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (907)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 6 5 (meaning884 q) (meaning907 q) (meaning921 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 907 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 907 = false ∨ valuation q 921 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 908 = false ∨ valuationOf q 922 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (908)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 6 6 (meaning884 q) (meaning908 q) (meaning922 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 908 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 908 = false ∨ valuation q 922 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 903 = false ∨ valuationOf q 918 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (885)) (literal (valuationOf q) (903)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 7 1 (meaning885 q) (meaning903 q) (meaning918 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 903 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 903 = false ∨ valuation q 918 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 904 = false ∨ valuationOf q 919 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (885)) (literal (valuationOf q) (904)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 7 2 (meaning885 q) (meaning904 q) (meaning919 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 904 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 904 = false ∨ valuation q 919 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 905 = false ∨ valuationOf q 920 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (885)) (literal (valuationOf q) (905)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 7 3 (meaning885 q) (meaning905 q) (meaning920 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 905 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 905 = false ∨ valuation q 920 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 906 = false ∨ valuationOf q 921 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (885)) (literal (valuationOf q) (906)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 7 4 (meaning885 q) (meaning906 q) (meaning921 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 906 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 906 = false ∨ valuation q 921 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 907 = false ∨ valuationOf q 922 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (885)) (literal (valuationOf q) (907)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 7 5 (meaning885 q) (meaning907 q) (meaning922 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 907 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 907 = false ∨ valuation q 922 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 908 = false ∨ valuationOf q 923 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (885)) (literal (valuationOf q) (908)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 7 6 (meaning885 q) (meaning908 q) (meaning923 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 908 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 908 = false ∨ valuation q 923 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 886 = false ∨ valuationOf q 903 = false ∨ valuationOf q 919 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (886)) (literal (valuationOf q) (903)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 8 1 (meaning886 q) (meaning903 q) (meaning919 q) hs
  change valuationOf q 886 = false ∨ valuationOf q 903 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 886 = false ∨ valuation q 903 = false ∨ valuation q 919 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 886 = false ∨ valuationOf q 904 = false ∨ valuationOf q 920 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (886)) (literal (valuationOf q) (904)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 8 2 (meaning886 q) (meaning904 q) (meaning920 q) hs
  change valuationOf q 886 = false ∨ valuationOf q 904 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 886 = false ∨ valuation q 904 = false ∨ valuation q 920 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 886 = false ∨ valuationOf q 905 = false ∨ valuationOf q 921 = true := by
  have hs : count911 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) + (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14]) (l₂ := [-15, -19, -22, -24, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (886)) (literal (valuationOf q) (905)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14]) (countLit q [-15, -19, -22, -24, -25, -27, -28, -31]) (count911 q) 8 3 (meaning886 q) (meaning905 q) (meaning921 q) hs
  change valuationOf q 886 = false ∨ valuationOf q 905 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 886 = false ∨ valuation q 905 = false ∨ valuation q 921 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 927 = true := by
  have hs : count927 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_right (literal (valuationOf q) (-34)) (literal (valuationOf q) (927)) (countLit q [-32]) (countLit q [-34]) (count927 q) 1 (meaningNeg34 q) (meaning927 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 927 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 34 = true ∨ valuationOf q 928 = true := by
  have hs : count927 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-34)) (literal (valuationOf q) (928)) (countLit q [-32]) (countLit q [-34]) (count927 q) 1 1 (meaningNeg32 q) (meaningNeg34 q) (meaning928 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 34)) = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 928 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 929 = true := by
  have hs : count929 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (929)) (countLit q [-35]) (countLit q [-36]) (count929 q) 1 (meaningNeg36 q) (meaning929 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 929 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 929 = true := by
  have hs : count929 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (929)) (countLit q [-35]) (countLit q [-36]) (count929 q) 1 (meaningNeg35 q) (meaning929 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 929 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 36 = true ∨ valuationOf q 930 = true := by
  have hs : count929 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (930)) (countLit q [-35]) (countLit q [-36]) (count929 q) 1 1 (meaningNeg35 q) (meaningNeg36 q) (meaning930 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 36 = true ∨ valuation q 930 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 927 = false ∨ valuationOf q 931 = true := by
  have hs : count931 q = (countLit q [-32, -34]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-35, -36])
  have hm := merge_left (literal (valuationOf q) (927)) (literal (valuationOf q) (931)) (countLit q [-32, -34]) (countLit q [-35, -36]) (count931 q) 1 (meaning927 q) (meaning931 q) hs
  change valuationOf q 927 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 927 = false ∨ valuation q 931 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 932 = true := by
  have hs : count931 q = (countLit q [-32, -34]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-35, -36])
  have hm := merge_left (literal (valuationOf q) (928)) (literal (valuationOf q) (932)) (countLit q [-32, -34]) (countLit q [-35, -36]) (count931 q) 2 (meaning928 q) (meaning932 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 932 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 929 = false ∨ valuationOf q 933 = true := by
  have hs : count931 q = (countLit q [-32, -34]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (928)) (literal (valuationOf q) (929)) (literal (valuationOf q) (933)) (countLit q [-32, -34]) (countLit q [-35, -36]) (count931 q) 2 1 (meaning928 q) (meaning929 q) (meaning933 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 929 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 929 = false ∨ valuation q 933 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 930 = false ∨ valuationOf q 934 = true := by
  have hs : count931 q = (countLit q [-32, -34]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (928)) (literal (valuationOf q) (930)) (literal (valuationOf q) (934)) (countLit q [-32, -34]) (countLit q [-35, -36]) (count931 q) 2 2 (meaning928 q) (meaning930 q) (meaning934 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 930 = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 930 = false ∨ valuation q 934 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 935 = true := by
  have hs : count935 q = (countLit q [-38]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (935)) (countLit q [-38]) (countLit q [-42]) (count935 q) 1 (meaningNeg38 q) (meaning935 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 935 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 42 = true ∨ valuationOf q 936 = true := by
  have hs : count935 q = (countLit q [-38]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (936)) (countLit q [-38]) (countLit q [-42]) (count935 q) 1 1 (meaningNeg38 q) (meaningNeg42 q) (meaning936 q) hs
  change (! (valuationOf q 38)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 42 = true ∨ valuation q 936 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 937 = true := by
  have hs : count937 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (937)) (countLit q [-43]) (countLit q [-44]) (count937 q) 1 (meaningNeg44 q) (meaning937 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 937 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E121.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112121
