import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 882 = false ∨ valuationOf q 892 = true := by
  have hs : count887 q = (countLit q [-1, -3, -4, -5, -8, -11, -12]) + (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12]) (l₂ := [-14, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (882)) (literal (valuationOf q) (892)) (countLit q [-1, -3, -4, -5, -8, -11, -12]) (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) (count887 q) 2 4 (meaning857 q) (meaning882 q) (meaning892 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 882 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 882 = false ∨ valuation q 892 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-1, -3, -4, -5, -8, -11, -12]) + (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12]) (l₂ := [-14, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_left (literal (valuationOf q) (858)) (literal (valuationOf q) (889)) (countLit q [-1, -3, -4, -5, -8, -11, -12]) (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) (count887 q) 3 (meaning858 q) (meaning889 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 889 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 879 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-1, -3, -4, -5, -8, -11, -12]) + (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12]) (l₂ := [-14, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (879)) (literal (valuationOf q) (890)) (countLit q [-1, -3, -4, -5, -8, -11, -12]) (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) (count887 q) 3 1 (meaning858 q) (meaning879 q) (meaning890 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 879 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 879 = false ∨ valuation q 890 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 880 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-1, -3, -4, -5, -8, -11, -12]) + (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12]) (l₂ := [-14, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (880)) (literal (valuationOf q) (891)) (countLit q [-1, -3, -4, -5, -8, -11, -12]) (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) (count887 q) 3 2 (meaning858 q) (meaning880 q) (meaning891 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 880 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 880 = false ∨ valuation q 891 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 881 = false ∨ valuationOf q 892 = true := by
  have hs : count887 q = (countLit q [-1, -3, -4, -5, -8, -11, -12]) + (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12]) (l₂ := [-14, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (881)) (literal (valuationOf q) (892)) (countLit q [-1, -3, -4, -5, -8, -11, -12]) (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) (count887 q) 3 3 (meaning858 q) (meaning881 q) (meaning892 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 881 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 881 = false ∨ valuation q 892 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-1, -3, -4, -5, -8, -11, -12]) + (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12]) (l₂ := [-14, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_left (literal (valuationOf q) (859)) (literal (valuationOf q) (890)) (countLit q [-1, -3, -4, -5, -8, -11, -12]) (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) (count887 q) 4 (meaning859 q) (meaning890 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 890 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 879 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-1, -3, -4, -5, -8, -11, -12]) + (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12]) (l₂ := [-14, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (859)) (literal (valuationOf q) (879)) (literal (valuationOf q) (891)) (countLit q [-1, -3, -4, -5, -8, -11, -12]) (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) (count887 q) 4 1 (meaning859 q) (meaning879 q) (meaning891 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 879 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 879 = false ∨ valuation q 891 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 880 = false ∨ valuationOf q 892 = true := by
  have hs : count887 q = (countLit q [-1, -3, -4, -5, -8, -11, -12]) + (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12]) (l₂ := [-14, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (859)) (literal (valuationOf q) (880)) (literal (valuationOf q) (892)) (countLit q [-1, -3, -4, -5, -8, -11, -12]) (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) (count887 q) 4 2 (meaning859 q) (meaning880 q) (meaning892 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 880 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 880 = false ∨ valuation q 892 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-1, -3, -4, -5, -8, -11, -12]) + (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12]) (l₂ := [-14, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_left (literal (valuationOf q) (860)) (literal (valuationOf q) (891)) (countLit q [-1, -3, -4, -5, -8, -11, -12]) (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) (count887 q) 5 (meaning860 q) (meaning891 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 891 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 902 = true := by
  have hs : count902 q = (countLit q [-32]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (902)) (countLit q [-32]) (countLit q [-35]) (count902 q) 1 (meaningNeg35 q) (meaning902 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 902 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 902 = true := by
  have hs : count902 q = (countLit q [-32]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (902)) (countLit q [-32]) (countLit q [-35]) (count902 q) 1 (meaningNeg32 q) (meaning902 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 902 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 35 = true ∨ valuationOf q 903 = true := by
  have hs : count902 q = (countLit q [-32]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (903)) (countLit q [-32]) (countLit q [-35]) (count902 q) 1 1 (meaningNeg32 q) (meaningNeg35 q) (meaning903 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 35 = true ∨ valuation q 903 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 904 = true := by
  have hs : count904 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (904)) (countLit q [-37]) (countLit q [-38]) (count904 q) 1 (meaningNeg38 q) (meaning904 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 904 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 904 = true := by
  have hs : count904 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (904)) (countLit q [-37]) (countLit q [-38]) (count904 q) 1 (meaningNeg37 q) (meaning904 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 904 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 38 = true ∨ valuationOf q 905 = true := by
  have hs : count904 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (905)) (countLit q [-37]) (countLit q [-38]) (count904 q) 1 1 (meaningNeg37 q) (meaningNeg38 q) (meaning905 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 905 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 904 = false ∨ valuationOf q 906 = true := by
  have hs : count906 q = (countLit q [-32, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -35]) (l₂ := [-37, -38])
  have hm := merge_right (literal (valuationOf q) (904)) (literal (valuationOf q) (906)) (countLit q [-32, -35]) (countLit q [-37, -38]) (count906 q) 1 (meaning904 q) (meaning906 q) hs
  change valuationOf q 904 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 904 = false ∨ valuation q 906 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 905 = false ∨ valuationOf q 907 = true := by
  have hs : count906 q = (countLit q [-32, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -35]) (l₂ := [-37, -38])
  have hm := merge_right (literal (valuationOf q) (905)) (literal (valuationOf q) (907)) (countLit q [-32, -35]) (countLit q [-37, -38]) (count906 q) 2 (meaning905 q) (meaning907 q) hs
  change valuationOf q 905 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 905 = false ∨ valuation q 907 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 906 = true := by
  have hs : count906 q = (countLit q [-32, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -35]) (l₂ := [-37, -38])
  have hm := merge_left (literal (valuationOf q) (902)) (literal (valuationOf q) (906)) (countLit q [-32, -35]) (countLit q [-37, -38]) (count906 q) 1 (meaning902 q) (meaning906 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 906 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 904 = false ∨ valuationOf q 907 = true := by
  have hs : count906 q = (countLit q [-32, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -35]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (902)) (literal (valuationOf q) (904)) (literal (valuationOf q) (907)) (countLit q [-32, -35]) (countLit q [-37, -38]) (count906 q) 1 1 (meaning902 q) (meaning904 q) (meaning907 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 904 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 904 = false ∨ valuation q 907 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 905 = false ∨ valuationOf q 908 = true := by
  have hs : count906 q = (countLit q [-32, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -35]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (902)) (literal (valuationOf q) (905)) (literal (valuationOf q) (908)) (countLit q [-32, -35]) (countLit q [-37, -38]) (count906 q) 1 2 (meaning902 q) (meaning905 q) (meaning908 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 905 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 905 = false ∨ valuation q 908 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 903 = false ∨ valuationOf q 907 = true := by
  have hs : count906 q = (countLit q [-32, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -35]) (l₂ := [-37, -38])
  have hm := merge_left (literal (valuationOf q) (903)) (literal (valuationOf q) (907)) (countLit q [-32, -35]) (countLit q [-37, -38]) (count906 q) 2 (meaning903 q) (meaning907 q) hs
  change valuationOf q 903 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 903 = false ∨ valuation q 907 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 903 = false ∨ valuationOf q 904 = false ∨ valuationOf q 908 = true := by
  have hs : count906 q = (countLit q [-32, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -35]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (903)) (literal (valuationOf q) (904)) (literal (valuationOf q) (908)) (countLit q [-32, -35]) (countLit q [-37, -38]) (count906 q) 2 1 (meaning903 q) (meaning904 q) (meaning908 q) hs
  change valuationOf q 903 = false ∨ valuationOf q 904 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 903 = false ∨ valuation q 904 = false ∨ valuation q 908 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 903 = false ∨ valuationOf q 905 = false ∨ valuationOf q 909 = true := by
  have hs : count906 q = (countLit q [-32, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -35]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (903)) (literal (valuationOf q) (905)) (literal (valuationOf q) (909)) (countLit q [-32, -35]) (countLit q [-37, -38]) (count906 q) 2 2 (meaning903 q) (meaning905 q) (meaning909 q) hs
  change valuationOf q 903 = false ∨ valuationOf q 905 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 903 = false ∨ valuation q 905 = false ∨ valuation q 909 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 910 = true := by
  have hs : count910 q = (countLit q [-39]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-43])
  have hm := merge_right (literal (valuationOf q) (-43)) (literal (valuationOf q) (910)) (countLit q [-39]) (countLit q [-43]) (count910 q) 1 (meaningNeg43 q) (meaning910 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 910 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 910 = true := by
  have hs : count910 q = (countLit q [-39]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-43])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (910)) (countLit q [-39]) (countLit q [-43]) (count910 q) 1 (meaningNeg39 q) (meaning910 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 910 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 43 = true ∨ valuationOf q 911 = true := by
  have hs : count910 q = (countLit q [-39]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-43])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-43)) (literal (valuationOf q) (911)) (countLit q [-39]) (countLit q [-43]) (count910 q) 1 1 (meaningNeg39 q) (meaningNeg43 q) (meaning911 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 43)) = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 43 = true ∨ valuation q 911 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 912 = true := by
  have hs : count912 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (912)) (countLit q [-45]) (countLit q [-46]) (count912 q) 1 (meaningNeg46 q) (meaning912 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 912 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 912 = true := by
  have hs : count912 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (912)) (countLit q [-45]) (countLit q [-46]) (count912 q) 1 (meaningNeg45 q) (meaning912 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 912 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 46 = true ∨ valuationOf q 913 = true := by
  have hs : count912 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (913)) (countLit q [-45]) (countLit q [-46]) (count912 q) 1 1 (meaningNeg45 q) (meaningNeg46 q) (meaning913 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 46 = true ∨ valuation q 913 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 914 = true := by
  have hs : count914 q = (countLit q [-39, -43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-39, -43]) (l₂ := [-45, -46])
  have hm := merge_right (literal (valuationOf q) (912)) (literal (valuationOf q) (914)) (countLit q [-39, -43]) (countLit q [-45, -46]) (count914 q) 1 (meaning912 q) (meaning914 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 914 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 914 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 913 = false ∨ valuationOf q 915 = true := by
  have hs : count914 q = (countLit q [-39, -43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-39, -43]) (l₂ := [-45, -46])
  have hm := merge_right (literal (valuationOf q) (913)) (literal (valuationOf q) (915)) (countLit q [-39, -43]) (countLit q [-45, -46]) (count914 q) 2 (meaning913 q) (meaning915 q) hs
  change valuationOf q 913 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 913 = false ∨ valuation q 915 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 914 = true := by
  have hs : count914 q = (countLit q [-39, -43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-39, -43]) (l₂ := [-45, -46])
  have hm := merge_left (literal (valuationOf q) (910)) (literal (valuationOf q) (914)) (countLit q [-39, -43]) (countLit q [-45, -46]) (count914 q) 1 (meaning910 q) (meaning914 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 914 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 914 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E153.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112153
