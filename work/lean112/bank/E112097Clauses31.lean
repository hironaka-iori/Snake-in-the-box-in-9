import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 892 = true := by
  have hs : count892 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (892)) (countLit q [-34]) (countLit q [-36]) (count892 q) 1 (meaningNeg34 q) (meaning892 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 892 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 36 = true ∨ valuationOf q 893 = true := by
  have hs : count892 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (893)) (countLit q [-34]) (countLit q [-36]) (count892 q) 1 1 (meaningNeg34 q) (meaningNeg36 q) (meaning893 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 36 = true ∨ valuation q 893 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 894 = true := by
  have hs : count894 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (892)) (literal (valuationOf q) (894)) (countLit q [-33]) (countLit q [-34, -36]) (count894 q) 1 (meaning892 q) (meaning894 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 894 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 893 = false ∨ valuationOf q 895 = true := by
  have hs : count894 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (893)) (literal (valuationOf q) (895)) (countLit q [-33]) (countLit q [-34, -36]) (count894 q) 2 (meaning893 q) (meaning895 q) hs
  change valuationOf q 893 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 893 = false ∨ valuation q 895 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 894 = true := by
  have hs : count894 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (894)) (countLit q [-33]) (countLit q [-34, -36]) (count894 q) 1 (meaningNeg33 q) (meaning894 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 894 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 892 = false ∨ valuationOf q 895 = true := by
  have hs : count894 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (892)) (literal (valuationOf q) (895)) (countLit q [-33]) (countLit q [-34, -36]) (count894 q) 1 1 (meaningNeg33 q) (meaning892 q) (meaning895 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 892 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 892 = false ∨ valuation q 895 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 893 = false ∨ valuationOf q 896 = true := by
  have hs : count894 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (893)) (literal (valuationOf q) (896)) (countLit q [-33]) (countLit q [-34, -36]) (count894 q) 1 2 (meaningNeg33 q) (meaning893 q) (meaning896 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 893 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 893 = false ∨ valuation q 896 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 897 = true := by
  have hs : count897 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (897)) (countLit q [-38]) (countLit q [-40]) (count897 q) 1 (meaningNeg40 q) (meaning897 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 897 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 897 = true := by
  have hs : count897 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (897)) (countLit q [-38]) (countLit q [-40]) (count897 q) 1 (meaningNeg38 q) (meaning897 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 897 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 40 = true ∨ valuationOf q 898 = true := by
  have hs : count897 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (-40)) (literal (valuationOf q) (898)) (countLit q [-38]) (countLit q [-40]) (count897 q) 1 1 (meaningNeg38 q) (meaningNeg40 q) (meaning898 q) hs
  change (! (valuationOf q 38)) = false ∨ (! (valuationOf q 40)) = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 898 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 899 = true := by
  have hs : count899 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (899)) (countLit q [-43]) (countLit q [-44]) (count899 q) 1 (meaningNeg44 q) (meaning899 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 899 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 899 = true := by
  have hs : count899 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (899)) (countLit q [-43]) (countLit q [-44]) (count899 q) 1 (meaningNeg43 q) (meaning899 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 899 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 44 = true ∨ valuationOf q 900 = true := by
  have hs : count899 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (900)) (countLit q [-43]) (countLit q [-44]) (count899 q) 1 1 (meaningNeg43 q) (meaningNeg44 q) (meaning900 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 900 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 901 = true := by
  have hs : count901 q = (countLit q [-38, -40]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-43, -44])
  have hm := merge_right (literal (valuationOf q) (899)) (literal (valuationOf q) (901)) (countLit q [-38, -40]) (countLit q [-43, -44]) (count901 q) 1 (meaning899 q) (meaning901 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 901 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 902 = true := by
  have hs : count901 q = (countLit q [-38, -40]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-43, -44])
  have hm := merge_right (literal (valuationOf q) (900)) (literal (valuationOf q) (902)) (countLit q [-38, -40]) (countLit q [-43, -44]) (count901 q) 2 (meaning900 q) (meaning902 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 902 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 901 = true := by
  have hs : count901 q = (countLit q [-38, -40]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-43, -44])
  have hm := merge_left (literal (valuationOf q) (897)) (literal (valuationOf q) (901)) (countLit q [-38, -40]) (countLit q [-43, -44]) (count901 q) 1 (meaning897 q) (meaning901 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 901 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 899 = false ∨ valuationOf q 902 = true := by
  have hs : count901 q = (countLit q [-38, -40]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (899)) (literal (valuationOf q) (902)) (countLit q [-38, -40]) (countLit q [-43, -44]) (count901 q) 1 1 (meaning897 q) (meaning899 q) (meaning902 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 899 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 899 = false ∨ valuation q 902 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 900 = false ∨ valuationOf q 903 = true := by
  have hs : count901 q = (countLit q [-38, -40]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (900)) (literal (valuationOf q) (903)) (countLit q [-38, -40]) (countLit q [-43, -44]) (count901 q) 1 2 (meaning897 q) (meaning900 q) (meaning903 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 900 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 900 = false ∨ valuation q 903 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 902 = true := by
  have hs : count901 q = (countLit q [-38, -40]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-43, -44])
  have hm := merge_left (literal (valuationOf q) (898)) (literal (valuationOf q) (902)) (countLit q [-38, -40]) (countLit q [-43, -44]) (count901 q) 2 (meaning898 q) (meaning902 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 902 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 899 = false ∨ valuationOf q 903 = true := by
  have hs : count901 q = (countLit q [-38, -40]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (899)) (literal (valuationOf q) (903)) (countLit q [-38, -40]) (countLit q [-43, -44]) (count901 q) 2 1 (meaning898 q) (meaning899 q) (meaning903 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 899 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 899 = false ∨ valuation q 903 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 901 = false ∨ valuationOf q 905 = true := by
  have hs : count905 q = (countLit q [-33, -34, -36]) + (countLit q [-38, -40, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-38, -40, -43, -44])
  have hm := merge_right (literal (valuationOf q) (901)) (literal (valuationOf q) (905)) (countLit q [-33, -34, -36]) (countLit q [-38, -40, -43, -44]) (count905 q) 1 (meaning901 q) (meaning905 q) hs
  change valuationOf q 901 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 901 = false ∨ valuation q 905 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 906 = true := by
  have hs : count905 q = (countLit q [-33, -34, -36]) + (countLit q [-38, -40, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-38, -40, -43, -44])
  have hm := merge_right (literal (valuationOf q) (902)) (literal (valuationOf q) (906)) (countLit q [-33, -34, -36]) (countLit q [-38, -40, -43, -44]) (count905 q) 2 (meaning902 q) (meaning906 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 906 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 903 = false ∨ valuationOf q 907 = true := by
  have hs : count905 q = (countLit q [-33, -34, -36]) + (countLit q [-38, -40, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-38, -40, -43, -44])
  have hm := merge_right (literal (valuationOf q) (903)) (literal (valuationOf q) (907)) (countLit q [-33, -34, -36]) (countLit q [-38, -40, -43, -44]) (count905 q) 3 (meaning903 q) (meaning907 q) hs
  change valuationOf q 903 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 903 = false ∨ valuation q 907 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 901 = false ∨ valuationOf q 906 = true := by
  have hs : count905 q = (countLit q [-33, -34, -36]) + (countLit q [-38, -40, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-38, -40, -43, -44])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (901)) (literal (valuationOf q) (906)) (countLit q [-33, -34, -36]) (countLit q [-38, -40, -43, -44]) (count905 q) 1 1 (meaning894 q) (meaning901 q) (meaning906 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 901 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 901 = false ∨ valuation q 906 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 902 = false ∨ valuationOf q 907 = true := by
  have hs : count905 q = (countLit q [-33, -34, -36]) + (countLit q [-38, -40, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-38, -40, -43, -44])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (902)) (literal (valuationOf q) (907)) (countLit q [-33, -34, -36]) (countLit q [-38, -40, -43, -44]) (count905 q) 1 2 (meaning894 q) (meaning902 q) (meaning907 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 902 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 902 = false ∨ valuation q 907 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 903 = false ∨ valuationOf q 908 = true := by
  have hs : count905 q = (countLit q [-33, -34, -36]) + (countLit q [-38, -40, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-38, -40, -43, -44])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (903)) (literal (valuationOf q) (908)) (countLit q [-33, -34, -36]) (countLit q [-38, -40, -43, -44]) (count905 q) 1 3 (meaning894 q) (meaning903 q) (meaning908 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 903 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 903 = false ∨ valuation q 908 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 906 = true := by
  have hs : count905 q = (countLit q [-33, -34, -36]) + (countLit q [-38, -40, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-38, -40, -43, -44])
  have hm := merge_left (literal (valuationOf q) (895)) (literal (valuationOf q) (906)) (countLit q [-33, -34, -36]) (countLit q [-38, -40, -43, -44]) (count905 q) 2 (meaning895 q) (meaning906 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 906 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 901 = false ∨ valuationOf q 907 = true := by
  have hs : count905 q = (countLit q [-33, -34, -36]) + (countLit q [-38, -40, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-38, -40, -43, -44])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (901)) (literal (valuationOf q) (907)) (countLit q [-33, -34, -36]) (countLit q [-38, -40, -43, -44]) (count905 q) 2 1 (meaning895 q) (meaning901 q) (meaning907 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 901 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 901 = false ∨ valuation q 907 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 902 = false ∨ valuationOf q 908 = true := by
  have hs : count905 q = (countLit q [-33, -34, -36]) + (countLit q [-38, -40, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-38, -40, -43, -44])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (902)) (literal (valuationOf q) (908)) (countLit q [-33, -34, -36]) (countLit q [-38, -40, -43, -44]) (count905 q) 2 2 (meaning895 q) (meaning902 q) (meaning908 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 902 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 902 = false ∨ valuation q 908 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 903 = false ∨ valuationOf q 909 = true := by
  have hs : count905 q = (countLit q [-33, -34, -36]) + (countLit q [-38, -40, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-38, -40, -43, -44])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (903)) (literal (valuationOf q) (909)) (countLit q [-33, -34, -36]) (countLit q [-38, -40, -43, -44]) (count905 q) 2 3 (meaning895 q) (meaning903 q) (meaning909 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 903 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 903 = false ∨ valuation q 909 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 901 = false ∨ valuationOf q 908 = true := by
  have hs : count905 q = (countLit q [-33, -34, -36]) + (countLit q [-38, -40, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-38, -40, -43, -44])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (901)) (literal (valuationOf q) (908)) (countLit q [-33, -34, -36]) (countLit q [-38, -40, -43, -44]) (count905 q) 3 1 (meaning896 q) (meaning901 q) (meaning908 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 901 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 901 = false ∨ valuation q 908 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 902 = false ∨ valuationOf q 909 = true := by
  have hs : count905 q = (countLit q [-33, -34, -36]) + (countLit q [-38, -40, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36]) (l₂ := [-38, -40, -43, -44])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (902)) (literal (valuationOf q) (909)) (countLit q [-33, -34, -36]) (countLit q [-38, -40, -43, -44]) (count905 q) 3 2 (meaning896 q) (meaning902 q) (meaning909 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 902 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 902 = false ∨ valuation q 909 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E097.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112097
