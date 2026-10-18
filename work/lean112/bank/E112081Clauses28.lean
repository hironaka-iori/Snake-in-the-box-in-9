import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 889 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (889)) (literal (valuationOf q) (903)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 6 3 (meaning869 q) (meaning889 q) (meaning903 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 889 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 889 = false ∨ valuation q 903 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 890 = false ∨ valuationOf q 904 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (890)) (literal (valuationOf q) (904)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 6 4 (meaning869 q) (meaning890 q) (meaning904 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 890 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 890 = false ∨ valuation q 904 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 891 = false ∨ valuationOf q 905 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (891)) (literal (valuationOf q) (905)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 6 5 (meaning869 q) (meaning891 q) (meaning905 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 891 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 891 = false ∨ valuation q 905 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 892 = false ∨ valuationOf q 906 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (892)) (literal (valuationOf q) (906)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 6 6 (meaning869 q) (meaning892 q) (meaning906 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 892 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 892 = false ∨ valuation q 906 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 888 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (888)) (literal (valuationOf q) (903)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 7 2 (meaning870 q) (meaning888 q) (meaning903 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 888 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 888 = false ∨ valuation q 903 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 889 = false ∨ valuationOf q 904 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (889)) (literal (valuationOf q) (904)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 7 3 (meaning870 q) (meaning889 q) (meaning904 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 889 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 889 = false ∨ valuation q 904 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 890 = false ∨ valuationOf q 905 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (890)) (literal (valuationOf q) (905)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 7 4 (meaning870 q) (meaning890 q) (meaning905 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 890 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 890 = false ∨ valuation q 905 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 892 = false ∨ valuationOf q 907 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (892)) (literal (valuationOf q) (907)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 7 6 (meaning870 q) (meaning892 q) (meaning907 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 892 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 892 = false ∨ valuation q 907 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 903 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (838)) (literal (valuationOf q) (903)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 2 9 (meaning838 q) (meaning903 q) (meaning920 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 903 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 903 = false ∨ valuation q 920 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 904 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (838)) (literal (valuationOf q) (904)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 2 10 (meaning838 q) (meaning904 q) (meaning921 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 904 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 904 = false ∨ valuation q 921 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 898 = false ∨ valuationOf q 916 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (898)) (literal (valuationOf q) (916)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 3 4 (meaning839 q) (meaning898 q) (meaning916 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 898 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 898 = false ∨ valuation q 916 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 899 = false ∨ valuationOf q 917 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (899)) (literal (valuationOf q) (917)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 3 5 (meaning839 q) (meaning899 q) (meaning917 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 899 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 899 = false ∨ valuation q 917 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 900 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (900)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 3 6 (meaning839 q) (meaning900 q) (meaning918 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 900 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 900 = false ∨ valuation q 918 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 901 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (901)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 3 7 (meaning839 q) (meaning901 q) (meaning919 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 901 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 901 = false ∨ valuation q 919 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 902 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (902)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 3 8 (meaning839 q) (meaning902 q) (meaning920 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 902 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 902 = false ∨ valuation q 920 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 903 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (903)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 3 9 (meaning839 q) (meaning903 q) (meaning921 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 903 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 903 = false ∨ valuation q 921 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 904 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (904)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 3 10 (meaning839 q) (meaning904 q) (meaning922 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 904 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 904 = false ∨ valuation q 922 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 898 = false ∨ valuationOf q 917 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (898)) (literal (valuationOf q) (917)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 4 4 (meaning840 q) (meaning898 q) (meaning917 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 898 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 898 = false ∨ valuation q 917 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 899 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (899)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 4 5 (meaning840 q) (meaning899 q) (meaning918 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 899 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 899 = false ∨ valuation q 918 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 900 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (900)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 4 6 (meaning840 q) (meaning900 q) (meaning919 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 900 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 900 = false ∨ valuation q 919 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 901 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (901)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 4 7 (meaning840 q) (meaning901 q) (meaning920 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 901 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 901 = false ∨ valuation q 920 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 902 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (902)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 4 8 (meaning840 q) (meaning902 q) (meaning921 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 902 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 902 = false ∨ valuation q 921 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 903 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (903)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 4 9 (meaning840 q) (meaning903 q) (meaning922 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 903 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 903 = false ∨ valuation q 922 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 904 = false ∨ valuationOf q 923 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (904)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 4 10 (meaning840 q) (meaning904 q) (meaning923 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 904 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 904 = false ∨ valuation q 923 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 905 = false ∨ valuationOf q 924 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (905)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 4 11 (meaning840 q) (meaning905 q) (meaning924 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 905 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 905 = false ∨ valuation q 924 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 906 = false ∨ valuationOf q 925 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (906)) (literal (valuationOf q) (925)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 4 12 (meaning840 q) (meaning906 q) (meaning925 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 906 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 906 = false ∨ valuation q 925 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 907 = false ∨ valuationOf q 926 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (907)) (literal (valuationOf q) (926)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 4 13 (meaning840 q) (meaning907 q) (meaning926 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 907 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 907 = false ∨ valuation q 926 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 898 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (898)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 5 4 (meaning841 q) (meaning898 q) (meaning918 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 898 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 898 = false ∨ valuation q 918 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 899 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (899)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 5 5 (meaning841 q) (meaning899 q) (meaning919 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 899 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 899 = false ∨ valuation q 919 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 900 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (900)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 5 6 (meaning841 q) (meaning900 q) (meaning920 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 900 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 900 = false ∨ valuation q 920 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 901 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (901)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 5 7 (meaning841 q) (meaning901 q) (meaning921 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 901 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 901 = false ∨ valuation q 921 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 902 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (902)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 5 8 (meaning841 q) (meaning902 q) (meaning922 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 902 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 902 = false ∨ valuation q 922 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E081.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112081
