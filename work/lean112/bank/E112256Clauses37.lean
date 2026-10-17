import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 884 = false ∨ valuationOf q 891 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (884)) (literal (valuationOf q) (891)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 3 4 (meaning875 q) (meaning884 q) (meaning891 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 884 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 884 = false ∨ valuation q 891 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 881 = false ∨ valuationOf q 889 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (881)) (literal (valuationOf q) (889)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 4 1 (meaning876 q) (meaning881 q) (meaning889 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 881 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 881 = false ∨ valuation q 889 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 882 = false ∨ valuationOf q 890 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (882)) (literal (valuationOf q) (890)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 4 2 (meaning876 q) (meaning882 q) (meaning890 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 882 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 882 = false ∨ valuation q 890 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 883 = false ∨ valuationOf q 891 = true := by
  have hs : count885 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (883)) (literal (valuationOf q) (891)) (countLit q [-15, -18, -19, -21]) (countLit q [-23, -25, -28, -30]) (count885 q) 4 3 (meaning876 q) (meaning883 q) (meaning891 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 883 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 883 = false ∨ valuation q 891 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 893 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (885)) (literal (valuationOf q) (893)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 1 (meaning885 q) (meaning893 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 893 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 886 = false ∨ valuationOf q 894 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (886)) (literal (valuationOf q) (894)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 2 (meaning886 q) (meaning894 q) hs
  change valuationOf q 886 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 886 = false ∨ valuation q 894 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 895 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (887)) (literal (valuationOf q) (895)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 3 (meaning887 q) (meaning895 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 895 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 888 = false ∨ valuationOf q 896 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (888)) (literal (valuationOf q) (896)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 4 (meaning888 q) (meaning896 q) hs
  change valuationOf q 888 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 888 = false ∨ valuation q 896 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 897 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (889)) (literal (valuationOf q) (897)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 5 (meaning889 q) (meaning897 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 897 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 885 = false ∨ valuationOf q 894 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (885)) (literal (valuationOf q) (894)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 1 1 (meaning862 q) (meaning885 q) (meaning894 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 885 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 885 = false ∨ valuation q 894 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 886 = false ∨ valuationOf q 895 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (886)) (literal (valuationOf q) (895)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 1 2 (meaning862 q) (meaning886 q) (meaning895 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 886 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 886 = false ∨ valuation q 895 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 887 = false ∨ valuationOf q 896 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (887)) (literal (valuationOf q) (896)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 1 3 (meaning862 q) (meaning887 q) (meaning896 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 887 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 887 = false ∨ valuation q 896 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 888 = false ∨ valuationOf q 897 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (888)) (literal (valuationOf q) (897)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 1 4 (meaning862 q) (meaning888 q) (meaning897 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 888 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 888 = false ∨ valuation q 897 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 889 = false ∨ valuationOf q 898 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (889)) (literal (valuationOf q) (898)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 1 5 (meaning862 q) (meaning889 q) (meaning898 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 889 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 889 = false ∨ valuation q 898 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 890 = false ∨ valuationOf q 899 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (890)) (literal (valuationOf q) (899)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 1 6 (meaning862 q) (meaning890 q) (meaning899 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 890 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 890 = false ∨ valuation q 899 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 894 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (863)) (literal (valuationOf q) (894)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 2 (meaning863 q) (meaning894 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 894 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 885 = false ∨ valuationOf q 895 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (885)) (literal (valuationOf q) (895)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 2 1 (meaning863 q) (meaning885 q) (meaning895 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 885 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 885 = false ∨ valuation q 895 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 886 = false ∨ valuationOf q 896 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (886)) (literal (valuationOf q) (896)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 2 2 (meaning863 q) (meaning886 q) (meaning896 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 886 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 886 = false ∨ valuation q 896 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 887 = false ∨ valuationOf q 897 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (887)) (literal (valuationOf q) (897)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 2 3 (meaning863 q) (meaning887 q) (meaning897 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 887 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 887 = false ∨ valuation q 897 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 888 = false ∨ valuationOf q 898 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (888)) (literal (valuationOf q) (898)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 2 4 (meaning863 q) (meaning888 q) (meaning898 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 888 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 888 = false ∨ valuation q 898 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 889 = false ∨ valuationOf q 899 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (889)) (literal (valuationOf q) (899)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 2 5 (meaning863 q) (meaning889 q) (meaning899 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 889 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 889 = false ∨ valuation q 899 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 890 = false ∨ valuationOf q 900 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (890)) (literal (valuationOf q) (900)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 2 6 (meaning863 q) (meaning890 q) (meaning900 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 890 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 890 = false ∨ valuation q 900 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 891 = false ∨ valuationOf q 901 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (891)) (literal (valuationOf q) (901)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 2 7 (meaning863 q) (meaning891 q) (meaning901 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 891 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 891 = false ∨ valuation q 901 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 895 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (864)) (literal (valuationOf q) (895)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 3 (meaning864 q) (meaning895 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 895 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 885 = false ∨ valuationOf q 896 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (885)) (literal (valuationOf q) (896)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 3 1 (meaning864 q) (meaning885 q) (meaning896 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 885 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 885 = false ∨ valuation q 896 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 886 = false ∨ valuationOf q 897 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (886)) (literal (valuationOf q) (897)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 3 2 (meaning864 q) (meaning886 q) (meaning897 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 886 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 886 = false ∨ valuation q 897 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 887 = false ∨ valuationOf q 898 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (887)) (literal (valuationOf q) (898)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 3 3 (meaning864 q) (meaning887 q) (meaning898 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 887 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 887 = false ∨ valuation q 898 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 888 = false ∨ valuationOf q 899 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (888)) (literal (valuationOf q) (899)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 3 4 (meaning864 q) (meaning888 q) (meaning899 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 888 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 888 = false ∨ valuation q 899 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (889)) (literal (valuationOf q) (900)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 3 5 (meaning864 q) (meaning889 q) (meaning900 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 889 = false ∨ valuation q 900 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 890 = false ∨ valuationOf q 901 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (890)) (literal (valuationOf q) (901)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 3 6 (meaning864 q) (meaning890 q) (meaning901 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 890 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 890 = false ∨ valuation q 901 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 896 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (865)) (literal (valuationOf q) (896)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 4 (meaning865 q) (meaning896 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 896 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 885 = false ∨ valuationOf q 897 = true := by
  have hs : count893 q = (countLit q [-1, -2, -5, -7, -10, -11, -14]) + (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14]) (l₂ := [-15, -18, -19, -21, -23, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (885)) (literal (valuationOf q) (897)) (countLit q [-1, -2, -5, -7, -10, -11, -14]) (countLit q [-15, -18, -19, -21, -23, -25, -28, -30]) (count893 q) 4 1 (meaning865 q) (meaning885 q) (meaning897 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 885 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 885 = false ∨ valuation q 897 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E256.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112256
