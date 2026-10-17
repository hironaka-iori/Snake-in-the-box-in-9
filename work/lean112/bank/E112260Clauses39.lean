import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 894 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (863)) (literal (valuationOf q) (894)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 2 (meaning863 q) (meaning894 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 894 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 885 = false ∨ valuationOf q 895 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (885)) (literal (valuationOf q) (895)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 2 1 (meaning863 q) (meaning885 q) (meaning895 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 885 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 885 = false ∨ valuation q 895 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 886 = false ∨ valuationOf q 896 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (886)) (literal (valuationOf q) (896)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 2 2 (meaning863 q) (meaning886 q) (meaning896 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 886 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 886 = false ∨ valuation q 896 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 887 = false ∨ valuationOf q 897 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (887)) (literal (valuationOf q) (897)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 2 3 (meaning863 q) (meaning887 q) (meaning897 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 887 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 887 = false ∨ valuation q 897 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 888 = false ∨ valuationOf q 898 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (888)) (literal (valuationOf q) (898)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 2 4 (meaning863 q) (meaning888 q) (meaning898 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 888 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 888 = false ∨ valuation q 898 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 889 = false ∨ valuationOf q 899 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (889)) (literal (valuationOf q) (899)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 2 5 (meaning863 q) (meaning889 q) (meaning899 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 889 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 889 = false ∨ valuation q 899 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 890 = false ∨ valuationOf q 900 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (890)) (literal (valuationOf q) (900)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 2 6 (meaning863 q) (meaning890 q) (meaning900 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 890 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 890 = false ∨ valuation q 900 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 891 = false ∨ valuationOf q 901 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (891)) (literal (valuationOf q) (901)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 2 7 (meaning863 q) (meaning891 q) (meaning901 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 891 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 891 = false ∨ valuation q 901 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 895 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (864)) (literal (valuationOf q) (895)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 3 (meaning864 q) (meaning895 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 895 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 885 = false ∨ valuationOf q 896 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (885)) (literal (valuationOf q) (896)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 3 1 (meaning864 q) (meaning885 q) (meaning896 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 885 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 885 = false ∨ valuation q 896 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 886 = false ∨ valuationOf q 897 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (886)) (literal (valuationOf q) (897)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 3 2 (meaning864 q) (meaning886 q) (meaning897 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 886 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 886 = false ∨ valuation q 897 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 887 = false ∨ valuationOf q 898 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (887)) (literal (valuationOf q) (898)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 3 3 (meaning864 q) (meaning887 q) (meaning898 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 887 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 887 = false ∨ valuation q 898 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 888 = false ∨ valuationOf q 899 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (888)) (literal (valuationOf q) (899)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 3 4 (meaning864 q) (meaning888 q) (meaning899 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 888 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 888 = false ∨ valuation q 899 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (889)) (literal (valuationOf q) (900)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 3 5 (meaning864 q) (meaning889 q) (meaning900 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 889 = false ∨ valuation q 900 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 896 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (865)) (literal (valuationOf q) (896)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 4 (meaning865 q) (meaning896 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 896 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 885 = false ∨ valuationOf q 897 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (885)) (literal (valuationOf q) (897)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 4 1 (meaning865 q) (meaning885 q) (meaning897 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 885 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 885 = false ∨ valuation q 897 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 886 = false ∨ valuationOf q 898 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (886)) (literal (valuationOf q) (898)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 4 2 (meaning865 q) (meaning886 q) (meaning898 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 886 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 886 = false ∨ valuation q 898 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 887 = false ∨ valuationOf q 899 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (887)) (literal (valuationOf q) (899)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 4 3 (meaning865 q) (meaning887 q) (meaning899 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 887 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 887 = false ∨ valuation q 899 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 888 = false ∨ valuationOf q 900 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (888)) (literal (valuationOf q) (900)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 4 4 (meaning865 q) (meaning888 q) (meaning900 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 888 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 888 = false ∨ valuation q 900 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 889 = false ∨ valuationOf q 901 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (889)) (literal (valuationOf q) (901)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 4 5 (meaning865 q) (meaning889 q) (meaning901 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 889 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 889 = false ∨ valuation q 901 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 897 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (866)) (literal (valuationOf q) (897)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 5 (meaning866 q) (meaning897 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 897 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 885 = false ∨ valuationOf q 898 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (885)) (literal (valuationOf q) (898)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 5 1 (meaning866 q) (meaning885 q) (meaning898 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 885 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 885 = false ∨ valuation q 898 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 886 = false ∨ valuationOf q 899 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (886)) (literal (valuationOf q) (899)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 5 2 (meaning866 q) (meaning886 q) (meaning899 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 886 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 886 = false ∨ valuation q 899 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 887 = false ∨ valuationOf q 900 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (887)) (literal (valuationOf q) (900)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 5 3 (meaning866 q) (meaning887 q) (meaning900 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 887 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 887 = false ∨ valuation q 900 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 888 = false ∨ valuationOf q 901 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (888)) (literal (valuationOf q) (901)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 5 4 (meaning866 q) (meaning888 q) (meaning901 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 888 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 888 = false ∨ valuation q 901 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 889 = false ∨ valuationOf q 902 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (889)) (literal (valuationOf q) (902)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 5 5 (meaning866 q) (meaning889 q) (meaning902 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 889 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 889 = false ∨ valuation q 902 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 885 = false ∨ valuationOf q 899 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (885)) (literal (valuationOf q) (899)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 6 1 (meaning867 q) (meaning885 q) (meaning899 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 885 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 885 = false ∨ valuation q 899 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 886 = false ∨ valuationOf q 900 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (886)) (literal (valuationOf q) (900)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 6 2 (meaning867 q) (meaning886 q) (meaning900 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 886 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 886 = false ∨ valuation q 900 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 888 = false ∨ valuationOf q 902 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -6, -7, -10, -12]) + (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12]) (l₂ := [-15, -16, -20, -21, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (888)) (literal (valuationOf q) (902)) (countLit q [-1, -2, -5, -6, -7, -10, -12]) (countLit q [-15, -16, -20, -21, -24, -26, -28, -30]) (count893 q) 6 4 (meaning867 q) (meaning888 q) (meaning902 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 888 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 888 = false ∨ valuation q 902 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 908 = true := by
  have hs : count908 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (908)) (countLit q [-34]) (countLit q [-36]) (count908 q) 1 (meaningNeg36 q) (meaning908 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 908 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 908 = true := by
  have hs : count908 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (908)) (countLit q [-34]) (countLit q [-36]) (count908 q) 1 (meaningNeg34 q) (meaning908 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 908 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 36 = true ∨ valuationOf q 909 = true := by
  have hs : count908 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (909)) (countLit q [-34]) (countLit q [-36]) (count908 q) 1 1 (meaningNeg34 q) (meaningNeg36 q) (meaning909 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 36 = true ∨ valuation q 909 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E260.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112260
