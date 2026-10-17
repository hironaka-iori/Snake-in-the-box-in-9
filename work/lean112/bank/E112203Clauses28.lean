import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 892 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-29, -32, -33, -34, -36, -40, -41]) + (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -34, -36, -40, -41]) (l₂ := [-42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (892)) (literal (valuationOf q) (902)) (countLit q [-29, -32, -33, -34, -36, -40, -41]) (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) (count895 q) 2 6 (meaning865 q) (meaning892 q) (meaning902 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 892 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 892 = false ∨ valuation q 902 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 893 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-29, -32, -33, -34, -36, -40, -41]) + (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -34, -36, -40, -41]) (l₂ := [-42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (893)) (literal (valuationOf q) (903)) (countLit q [-29, -32, -33, -34, -36, -40, -41]) (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) (count895 q) 2 7 (meaning865 q) (meaning893 q) (meaning903 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 893 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 893 = false ∨ valuation q 903 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 894 = false ∨ valuationOf q 904 = true := by
  have hs : count895 q = (countLit q [-29, -32, -33, -34, -36, -40, -41]) + (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -34, -36, -40, -41]) (l₂ := [-42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (894)) (literal (valuationOf q) (904)) (countLit q [-29, -32, -33, -34, -36, -40, -41]) (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) (count895 q) 2 8 (meaning865 q) (meaning894 q) (meaning904 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 894 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 894 = false ∨ valuation q 904 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-29, -32, -33, -34, -36, -40, -41]) + (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -34, -36, -40, -41]) (l₂ := [-42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (889)) (literal (valuationOf q) (900)) (countLit q [-29, -32, -33, -34, -36, -40, -41]) (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) (count895 q) 3 3 (meaning866 q) (meaning889 q) (meaning900 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 889 = false ∨ valuation q 900 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 890 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-29, -32, -33, -34, -36, -40, -41]) + (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -34, -36, -40, -41]) (l₂ := [-42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (890)) (literal (valuationOf q) (901)) (countLit q [-29, -32, -33, -34, -36, -40, -41]) (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) (count895 q) 3 4 (meaning866 q) (meaning890 q) (meaning901 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 890 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 890 = false ∨ valuation q 901 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 891 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-29, -32, -33, -34, -36, -40, -41]) + (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -34, -36, -40, -41]) (l₂ := [-42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (891)) (literal (valuationOf q) (902)) (countLit q [-29, -32, -33, -34, -36, -40, -41]) (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) (count895 q) 3 5 (meaning866 q) (meaning891 q) (meaning902 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 891 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 891 = false ∨ valuation q 902 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 892 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-29, -32, -33, -34, -36, -40, -41]) + (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -34, -36, -40, -41]) (l₂ := [-42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (892)) (literal (valuationOf q) (903)) (countLit q [-29, -32, -33, -34, -36, -40, -41]) (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) (count895 q) 3 6 (meaning866 q) (meaning892 q) (meaning903 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 892 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 892 = false ∨ valuation q 903 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 893 = false ∨ valuationOf q 904 = true := by
  have hs : count895 q = (countLit q [-29, -32, -33, -34, -36, -40, -41]) + (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -34, -36, -40, -41]) (l₂ := [-42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (893)) (literal (valuationOf q) (904)) (countLit q [-29, -32, -33, -34, -36, -40, -41]) (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) (count895 q) 3 7 (meaning866 q) (meaning893 q) (meaning904 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 893 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 893 = false ∨ valuation q 904 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 894 = false ∨ valuationOf q 905 = true := by
  have hs : count895 q = (countLit q [-29, -32, -33, -34, -36, -40, -41]) + (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -34, -36, -40, -41]) (l₂ := [-42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (894)) (literal (valuationOf q) (905)) (countLit q [-29, -32, -33, -34, -36, -40, -41]) (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) (count895 q) 3 8 (meaning866 q) (meaning894 q) (meaning905 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 894 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 894 = false ∨ valuation q 905 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 889 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-29, -32, -33, -34, -36, -40, -41]) + (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -34, -36, -40, -41]) (l₂ := [-42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (889)) (literal (valuationOf q) (901)) (countLit q [-29, -32, -33, -34, -36, -40, -41]) (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) (count895 q) 4 3 (meaning867 q) (meaning889 q) (meaning901 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 889 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 889 = false ∨ valuation q 901 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 890 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-29, -32, -33, -34, -36, -40, -41]) + (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -34, -36, -40, -41]) (l₂ := [-42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (890)) (literal (valuationOf q) (902)) (countLit q [-29, -32, -33, -34, -36, -40, -41]) (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) (count895 q) 4 4 (meaning867 q) (meaning890 q) (meaning902 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 890 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 890 = false ∨ valuation q 902 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 891 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-29, -32, -33, -34, -36, -40, -41]) + (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -34, -36, -40, -41]) (l₂ := [-42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (891)) (literal (valuationOf q) (903)) (countLit q [-29, -32, -33, -34, -36, -40, -41]) (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) (count895 q) 4 5 (meaning867 q) (meaning891 q) (meaning903 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 891 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 891 = false ∨ valuation q 903 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 889 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-29, -32, -33, -34, -36, -40, -41]) + (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -34, -36, -40, -41]) (l₂ := [-42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (889)) (literal (valuationOf q) (902)) (countLit q [-29, -32, -33, -34, -36, -40, -41]) (countLit q [-42, -44, -46, -47, -48, -51, -52, -54]) (count895 q) 5 3 (meaning868 q) (meaning889 q) (meaning902 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 889 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 889 = false ∨ valuation q 902 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 899 = false ∨ valuationOf q 917 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (899)) (literal (valuationOf q) (917)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 3 5 (meaning839 q) (meaning899 q) (meaning917 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 899 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 899 = false ∨ valuation q 917 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 900 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (900)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 3 6 (meaning839 q) (meaning900 q) (meaning918 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 900 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 900 = false ∨ valuation q 918 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 901 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (901)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 3 7 (meaning839 q) (meaning901 q) (meaning919 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 901 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 901 = false ∨ valuation q 919 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 902 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (902)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 3 8 (meaning839 q) (meaning902 q) (meaning920 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 902 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 902 = false ∨ valuation q 920 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 903 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (903)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 3 9 (meaning839 q) (meaning903 q) (meaning921 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 903 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 903 = false ∨ valuation q 921 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 904 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (904)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 3 10 (meaning839 q) (meaning904 q) (meaning922 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 904 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 904 = false ∨ valuation q 922 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 898 = false ∨ valuationOf q 917 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (898)) (literal (valuationOf q) (917)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 4 4 (meaning840 q) (meaning898 q) (meaning917 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 898 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 898 = false ∨ valuation q 917 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 899 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (899)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 4 5 (meaning840 q) (meaning899 q) (meaning918 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 899 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 899 = false ∨ valuation q 918 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 900 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (900)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 4 6 (meaning840 q) (meaning900 q) (meaning919 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 900 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 900 = false ∨ valuation q 919 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 901 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (901)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 4 7 (meaning840 q) (meaning901 q) (meaning920 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 901 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 901 = false ∨ valuation q 920 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 902 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (902)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 4 8 (meaning840 q) (meaning902 q) (meaning921 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 902 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 902 = false ∨ valuation q 921 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 903 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (903)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 4 9 (meaning840 q) (meaning903 q) (meaning922 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 903 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 903 = false ∨ valuation q 922 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 904 = false ∨ valuationOf q 923 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (904)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 4 10 (meaning840 q) (meaning904 q) (meaning923 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 904 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 904 = false ∨ valuation q 923 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 905 = false ∨ valuationOf q 924 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (905)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 4 11 (meaning840 q) (meaning905 q) (meaning924 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 905 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 905 = false ∨ valuation q 924 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 898 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (898)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 5 4 (meaning841 q) (meaning898 q) (meaning918 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 898 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 898 = false ∨ valuation q 918 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 899 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (899)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 5 5 (meaning841 q) (meaning899 q) (meaning919 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 899 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 899 = false ∨ valuation q 919 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 900 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (900)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 5 6 (meaning841 q) (meaning900 q) (meaning920 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 900 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 900 = false ∨ valuation q 920 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 901 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (901)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 5 7 (meaning841 q) (meaning901 q) (meaning921 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 901 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 901 = false ∨ valuation q 921 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 902 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) + (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (l₂ := [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (902)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]) (countLit q [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]) (count910 q) 5 8 (meaning841 q) (meaning902 q) (meaning922 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 902 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 902 = false ∨ valuation q 922 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E203.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112203
