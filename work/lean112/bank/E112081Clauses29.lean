import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 903 = false ∨ valuationOf q 923 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (903)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 5 9 (meaning841 q) (meaning903 q) (meaning923 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 903 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 903 = false ∨ valuation q 923 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 904 = false ∨ valuationOf q 924 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (904)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 5 10 (meaning841 q) (meaning904 q) (meaning924 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 904 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 904 = false ∨ valuation q 924 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 899 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (899)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 6 5 (meaning842 q) (meaning899 q) (meaning920 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 899 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 899 = false ∨ valuation q 920 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 900 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (900)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 6 6 (meaning842 q) (meaning900 q) (meaning921 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 900 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 900 = false ∨ valuation q 921 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 901 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (901)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 6 7 (meaning842 q) (meaning901 q) (meaning922 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 901 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 901 = false ∨ valuation q 922 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 902 = false ∨ valuationOf q 923 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (902)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 6 8 (meaning842 q) (meaning902 q) (meaning923 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 902 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 902 = false ∨ valuation q 923 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 903 = false ∨ valuationOf q 924 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (903)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 6 9 (meaning842 q) (meaning903 q) (meaning924 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 903 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 903 = false ∨ valuation q 924 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 900 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (900)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 7 6 (meaning843 q) (meaning900 q) (meaning922 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 900 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 900 = false ∨ valuation q 922 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 901 = false ∨ valuationOf q 923 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (901)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 7 7 (meaning843 q) (meaning901 q) (meaning923 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 901 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 901 = false ∨ valuation q 923 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 902 = false ∨ valuationOf q 924 = true := by
  have hs : count910 q = (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) + (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (l₂ := [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (902)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -7, -9, -10, -14, -15, -17, -18, -20, -21, -25, -27, -29]) (countLit q [-30, -33, -34, -35, -37, -41, -42, -43, -45, -47, -48, -49, -52, -53, -55]) (count910 q) 7 8 (meaning843 q) (meaning902 q) (meaning924 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 902 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 902 = false ∨ valuation q 924 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 929 = true := by
  have hs : count929 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (929)) (countLit q [-60]) (countLit q [-62]) (count929 q) 1 (meaningNeg62 q) (meaning929 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 929 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 929 = true := by
  have hs : count929 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (929)) (countLit q [-60]) (countLit q [-62]) (count929 q) 1 (meaningNeg60 q) (meaning929 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 929 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 62 = true ∨ valuationOf q 930 = true := by
  have hs : count929 q = (countLit q [-60]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (930)) (countLit q [-60]) (countLit q [-62]) (count929 q) 1 1 (meaningNeg60 q) (meaningNeg62 q) (meaning930 q) hs
  change (! (valuationOf q 60)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 62 = true ∨ valuation q 930 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 929 = false ∨ valuationOf q 931 = true := by
  have hs : count931 q = (countLit q [-57]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60, -62])
  have hm := merge_right (literal (valuationOf q) (929)) (literal (valuationOf q) (931)) (countLit q [-57]) (countLit q [-60, -62]) (count931 q) 1 (meaning929 q) (meaning931 q) hs
  change valuationOf q 929 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 929 = false ∨ valuation q 931 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 930 = false ∨ valuationOf q 932 = true := by
  have hs : count931 q = (countLit q [-57]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60, -62])
  have hm := merge_right (literal (valuationOf q) (930)) (literal (valuationOf q) (932)) (countLit q [-57]) (countLit q [-60, -62]) (count931 q) 2 (meaning930 q) (meaning932 q) hs
  change valuationOf q 930 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 930 = false ∨ valuation q 932 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 931 = true := by
  have hs : count931 q = (countLit q [-57]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60, -62])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (931)) (countLit q [-57]) (countLit q [-60, -62]) (count931 q) 1 (meaningNeg57 q) (meaning931 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 931 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 929 = false ∨ valuationOf q 932 = true := by
  have hs : count931 q = (countLit q [-57]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60, -62])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (929)) (literal (valuationOf q) (932)) (countLit q [-57]) (countLit q [-60, -62]) (count931 q) 1 1 (meaningNeg57 q) (meaning929 q) (meaning932 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 929 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 929 = false ∨ valuation q 932 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 930 = false ∨ valuationOf q 933 = true := by
  have hs : count931 q = (countLit q [-57]) + (countLit q [-60, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60, -62])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (930)) (literal (valuationOf q) (933)) (countLit q [-57]) (countLit q [-60, -62]) (count931 q) 1 2 (meaningNeg57 q) (meaning930 q) (meaning933 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 930 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 930 = false ∨ valuation q 933 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 934 = true := by
  have hs : count934 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (934)) (countLit q [-65]) (countLit q [-66]) (count934 q) 1 (meaningNeg66 q) (meaning934 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 934 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 934 = true := by
  have hs : count934 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (934)) (countLit q [-65]) (countLit q [-66]) (count934 q) 1 (meaningNeg65 q) (meaning934 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 934 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 66 = true ∨ valuationOf q 935 = true := by
  have hs : count934 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (935)) (countLit q [-65]) (countLit q [-66]) (count934 q) 1 1 (meaningNeg65 q) (meaningNeg66 q) (meaning935 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 66 = true ∨ valuation q 935 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 936 = true := by
  have hs : count936 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (936)) (countLit q [-68]) (countLit q [-69]) (count936 q) 1 (meaningNeg69 q) (meaning936 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 936 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 936 = true := by
  have hs : count936 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (936)) (countLit q [-68]) (countLit q [-69]) (count936 q) 1 (meaningNeg68 q) (meaning936 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 936 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 69 = true ∨ valuationOf q 937 = true := by
  have hs : count936 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_two (literal (valuationOf q) (-68)) (literal (valuationOf q) (-69)) (literal (valuationOf q) (937)) (countLit q [-68]) (countLit q [-69]) (count936 q) 1 1 (meaningNeg68 q) (meaningNeg69 q) (meaning937 q) hs
  change (! (valuationOf q 68)) = false ∨ (! (valuationOf q 69)) = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 69 = true ∨ valuation q 937 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_right (literal (valuationOf q) (936)) (literal (valuationOf q) (938)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count938 q) 1 (meaning936 q) (meaning938 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 938 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_right (literal (valuationOf q) (937)) (literal (valuationOf q) (939)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count938 q) 2 (meaning937 q) (meaning939 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 939 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_left (literal (valuationOf q) (934)) (literal (valuationOf q) (938)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count938 q) 1 (meaning934 q) (meaning938 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 938 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 936 = false ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (936)) (literal (valuationOf q) (939)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count938 q) 1 1 (meaning934 q) (meaning936 q) (meaning939 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 936 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 936 = false ∨ valuation q 939 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 937 = false ∨ valuationOf q 940 = true := by
  have hs : count938 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (937)) (literal (valuationOf q) (940)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count938 q) 1 2 (meaning934 q) (meaning937 q) (meaning940 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 937 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 937 = false ∨ valuation q 940 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_left (literal (valuationOf q) (935)) (literal (valuationOf q) (939)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count938 q) 2 (meaning935 q) (meaning939 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 939 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 936 = false ∨ valuationOf q 940 = true := by
  have hs : count938 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (936)) (literal (valuationOf q) (940)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count938 q) 2 1 (meaning935 q) (meaning936 q) (meaning940 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 936 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 936 = false ∨ valuation q 940 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 937 = false ∨ valuationOf q 941 = true := by
  have hs : count938 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (937)) (literal (valuationOf q) (941)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count938 q) 2 2 (meaning935 q) (meaning937 q) (meaning941 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 937 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 937 = false ∨ valuation q 941 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E081.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112081
