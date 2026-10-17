import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 886 = false ∨ valuationOf q 898 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (886)) (literal (valuationOf q) (898)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 4 2 (meaning865 q) (meaning886 q) (meaning898 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 886 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 886 = false ∨ valuation q 898 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 887 = false ∨ valuationOf q 899 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (887)) (literal (valuationOf q) (899)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 4 3 (meaning865 q) (meaning887 q) (meaning899 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 887 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 887 = false ∨ valuation q 899 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 888 = false ∨ valuationOf q 900 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (888)) (literal (valuationOf q) (900)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 4 4 (meaning865 q) (meaning888 q) (meaning900 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 888 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 888 = false ∨ valuation q 900 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 889 = false ∨ valuationOf q 901 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (889)) (literal (valuationOf q) (901)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 4 5 (meaning865 q) (meaning889 q) (meaning901 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 889 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 889 = false ∨ valuation q 901 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 890 = false ∨ valuationOf q 902 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (890)) (literal (valuationOf q) (902)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 4 6 (meaning865 q) (meaning890 q) (meaning902 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 890 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 890 = false ∨ valuation q 902 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 897 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (866)) (literal (valuationOf q) (897)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 5 (meaning866 q) (meaning897 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 897 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 885 = false ∨ valuationOf q 898 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (885)) (literal (valuationOf q) (898)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 5 1 (meaning866 q) (meaning885 q) (meaning898 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 885 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 885 = false ∨ valuation q 898 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 886 = false ∨ valuationOf q 899 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (886)) (literal (valuationOf q) (899)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 5 2 (meaning866 q) (meaning886 q) (meaning899 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 886 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 886 = false ∨ valuation q 899 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 887 = false ∨ valuationOf q 900 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (887)) (literal (valuationOf q) (900)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 5 3 (meaning866 q) (meaning887 q) (meaning900 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 887 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 887 = false ∨ valuation q 900 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 888 = false ∨ valuationOf q 901 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (888)) (literal (valuationOf q) (901)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 5 4 (meaning866 q) (meaning888 q) (meaning901 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 888 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 888 = false ∨ valuation q 901 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 889 = false ∨ valuationOf q 902 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (889)) (literal (valuationOf q) (902)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 5 5 (meaning866 q) (meaning889 q) (meaning902 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 889 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 889 = false ∨ valuation q 902 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 898 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (867)) (literal (valuationOf q) (898)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 6 (meaning867 q) (meaning898 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 898 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 885 = false ∨ valuationOf q 899 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (885)) (literal (valuationOf q) (899)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 6 1 (meaning867 q) (meaning885 q) (meaning899 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 885 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 885 = false ∨ valuation q 899 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 886 = false ∨ valuationOf q 900 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (886)) (literal (valuationOf q) (900)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 6 2 (meaning867 q) (meaning886 q) (meaning900 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 886 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 886 = false ∨ valuation q 900 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 887 = false ∨ valuationOf q 901 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (887)) (literal (valuationOf q) (901)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 6 3 (meaning867 q) (meaning887 q) (meaning901 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 887 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 887 = false ∨ valuation q 901 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 888 = false ∨ valuationOf q 902 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (888)) (literal (valuationOf q) (902)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 6 4 (meaning867 q) (meaning888 q) (meaning902 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 888 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 888 = false ∨ valuation q 902 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 885 = false ∨ valuationOf q 900 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (885)) (literal (valuationOf q) (900)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 7 1 (meaning868 q) (meaning885 q) (meaning900 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 885 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 885 = false ∨ valuation q 900 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 887 = false ∨ valuationOf q 902 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (887)) (literal (valuationOf q) (902)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 7 3 (meaning868 q) (meaning887 q) (meaning902 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 887 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 887 = false ∨ valuation q 902 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 908 = true := by
  have hs : count908 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (908)) (countLit q [-34]) (countLit q [-36]) (count908 q) 1 (meaningNeg36 q) (meaning908 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 908 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 908 = true := by
  have hs : count908 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (908)) (countLit q [-34]) (countLit q [-36]) (count908 q) 1 (meaningNeg34 q) (meaning908 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 908 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 36 = true ∨ valuationOf q 909 = true := by
  have hs : count908 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (909)) (countLit q [-34]) (countLit q [-36]) (count908 q) 1 1 (meaningNeg34 q) (meaningNeg36 q) (meaning909 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 36 = true ∨ valuation q 909 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 910 = true := by
  have hs : count910 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (908)) (literal (valuationOf q) (910)) (countLit q [-33]) (countLit q [-34, -36]) (count910 q) 1 (meaning908 q) (meaning910 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 910 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 911 = true := by
  have hs : count910 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (909)) (literal (valuationOf q) (911)) (countLit q [-33]) (countLit q [-34, -36]) (count910 q) 2 (meaning909 q) (meaning911 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 911 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 910 = true := by
  have hs : count910 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (910)) (countLit q [-33]) (countLit q [-34, -36]) (count910 q) 1 (meaningNeg33 q) (meaning910 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 910 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 908 = false ∨ valuationOf q 911 = true := by
  have hs : count910 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (908)) (literal (valuationOf q) (911)) (countLit q [-33]) (countLit q [-34, -36]) (count910 q) 1 1 (meaningNeg33 q) (meaning908 q) (meaning911 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 908 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 908 = false ∨ valuation q 911 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 909 = false ∨ valuationOf q 912 = true := by
  have hs : count910 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (909)) (literal (valuationOf q) (912)) (countLit q [-33]) (countLit q [-34, -36]) (count910 q) 1 2 (meaningNeg33 q) (meaning909 q) (meaning912 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 909 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 909 = false ∨ valuation q 912 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 913 = true := by
  have hs : count913 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (913)) (countLit q [-41]) (countLit q [-42]) (count913 q) 1 (meaningNeg42 q) (meaning913 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 913 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 913 = true := by
  have hs : count913 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (913)) (countLit q [-41]) (countLit q [-42]) (count913 q) 1 (meaningNeg41 q) (meaning913 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 913 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 42 = true ∨ valuationOf q 914 = true := by
  have hs : count913 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (914)) (countLit q [-41]) (countLit q [-42]) (count913 q) 1 1 (meaningNeg41 q) (meaningNeg42 q) (meaning914 q) hs
  change (! (valuationOf q 41)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 914 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 42 = true ∨ valuation q 914 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 915 = true := by
  have hs : count915 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (915)) (countLit q [-43]) (countLit q [-44]) (count915 q) 1 (meaningNeg44 q) (meaning915 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 915 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 915 = true := by
  have hs : count915 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (915)) (countLit q [-43]) (countLit q [-44]) (count915 q) 1 (meaningNeg43 q) (meaning915 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 915 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 44 = true ∨ valuationOf q 916 = true := by
  have hs : count915 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (916)) (countLit q [-43]) (countLit q [-44]) (count915 q) 1 1 (meaningNeg43 q) (meaningNeg44 q) (meaning916 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 916 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E256.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112256
