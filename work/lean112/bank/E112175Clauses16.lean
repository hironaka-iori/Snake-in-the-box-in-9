import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-78]) + (countLit q [-82, -83]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-82, -83])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (883)) (countLit q [-78]) (countLit q [-82, -83]) (count883 q) 1 (meaningNeg78 q) (meaning883 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 883 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 886 = true := by
  have hs : count886 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (886)) (countLit q [-84]) (countLit q [-86]) (count886 q) 1 (meaningNeg84 q) (meaning886 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 886 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 886 = false ∨ valuationOf q 890 = true := by
  have hs : count890 q = (countLit q [-84, -86]) + (countLit q [-88, -89]) := List.countP_append (p := literal q) (l₁ := [-84, -86]) (l₂ := [-88, -89])
  have hm := merge_left (literal (valuationOf q) (886)) (literal (valuationOf q) (890)) (countLit q [-84, -86]) (countLit q [-88, -89]) (count890 q) 1 (meaning886 q) (meaning890 q) hs
  change valuationOf q 886 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 886 = false ∨ valuation q 890 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 890 = false ∨ valuationOf q 895 = true := by
  have hs : count894 q = (countLit q [-78, -82, -83]) + (countLit q [-84, -86, -88, -89]) := List.countP_append (p := literal q) (l₁ := [-78, -82, -83]) (l₂ := [-84, -86, -88, -89])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (890)) (literal (valuationOf q) (895)) (countLit q [-78, -82, -83]) (countLit q [-84, -86, -88, -89]) (count894 q) 1 1 (meaning883 q) (meaning890 q) (meaning895 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 890 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 890 = false ∨ valuation q 895 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 922 = true := by
  have hs : count921 q = (countLit q [-78, -82, -83, -84, -86, -88, -89]) + (countLit q [-91, -94, -96, -97, -98, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -82, -83, -84, -86, -88, -89]) (l₂ := [-91, -94, -96, -97, -98, -103, -104])
  have hm := merge_left (literal (valuationOf q) (895)) (literal (valuationOf q) (922)) (countLit q [-78, -82, -83, -84, -86, -88, -89]) (countLit q [-91, -94, -96, -97, -98, -103, -104]) (count921 q) 2 (meaning895 q) (meaning922 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 922 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 936 = true := by
  have hs : count935 q = (countLit q [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76]) + (countLit q [-78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76]) (l₂ := [-78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104])
  have hm := merge_right (literal (valuationOf q) (922)) (literal (valuationOf q) (936)) (countLit q [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76]) (countLit q [-78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]) (count935 q) 2 (meaning922 q) (meaning936 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 936 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 922 = false ∨ valuationOf q 937 = true := by
  have hs : count935 q = (countLit q [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76]) + (countLit q [-78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76]) (l₂ := [-78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (922)) (literal (valuationOf q) (937)) (countLit q [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76]) (countLit q [-78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]) (count935 q) 1 2 (meaning868 q) (meaning922 q) (meaning937 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 922 = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 922 = false ∨ valuation q 937 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 922 = false ∨ valuationOf q 938 = true := by
  have hs : count935 q = (countLit q [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76]) + (countLit q [-78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76]) (l₂ := [-78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (922)) (literal (valuationOf q) (938)) (countLit q [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76]) (countLit q [-78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]) (count935 q) 2 2 (meaning869 q) (meaning922 q) (meaning938 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 922 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 922 = false ∨ valuation q 938 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 938 = false ∨ valuationOf q 962 = true := by
  have hs : count949 q = (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24, -26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) + (countLit q [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76, -78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24, -26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) (l₂ := [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76, -78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (938)) (literal (valuationOf q) (962)) (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24, -26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) (countLit q [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76, -78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]) (count949 q) 10 4 (meaning827 q) (meaning938 q) (meaning962 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 938 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 938 = false ∨ valuation q 962 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 937 = false ∨ valuationOf q 962 = true := by
  have hs : count949 q = (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24, -26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) + (countLit q [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76, -78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24, -26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) (l₂ := [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76, -78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104])
  have hm := merge_two (literal (valuationOf q) (828)) (literal (valuationOf q) (937)) (literal (valuationOf q) (962)) (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24, -26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) (countLit q [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76, -78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]) (count949 q) 11 3 (meaning828 q) (meaning937 q) (meaning962 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 937 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 937 = false ∨ valuation q 962 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 829 = false ∨ valuationOf q 936 = false ∨ valuationOf q 962 = true := by
  have hs : count949 q = (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24, -26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) + (countLit q [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76, -78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24, -26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) (l₂ := [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76, -78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104])
  have hm := merge_two (literal (valuationOf q) (829)) (literal (valuationOf q) (936)) (literal (valuationOf q) (962)) (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24, -26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) (countLit q [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76, -78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]) (count949 q) 12 2 (meaning829 q) (meaning936 q) (meaning962 q) hs
  change valuationOf q 829 = false ∨ valuationOf q 936 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 829 = false ∨ valuation q 936 = false ∨ valuation q 962 = true := counterClause523 (baseVal q)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 962 = false := by
  rw [value962]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count949 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause525 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1241 = true := by
  have hs : count1241 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1241)) (countLit q [-6]) (countLit q [-7]) (count1241 q) 1 (meaningNeg7 q) (meaning1241 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1241 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1242 = true := by
  have hs : count1241 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1242)) (countLit q [-6]) (countLit q [-7]) (count1241 q) 1 1 (meaningNeg6 q) (meaningNeg7 q) (meaning1242 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 1242 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 1241 = false ∨ valuationOf q 1243 = true := by
  have hs : count1243 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_right (literal (valuationOf q) (1241)) (literal (valuationOf q) (1243)) (countLit q [-2]) (countLit q [-6, -7]) (count1243 q) 1 (meaning1241 q) (meaning1243 q) hs
  change valuationOf q 1241 = false ∨ valuationOf q 1243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 1241 = false ∨ valuation q 1243 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 1242 = false ∨ valuationOf q 1244 = true := by
  have hs : count1243 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_right (literal (valuationOf q) (1242)) (literal (valuationOf q) (1244)) (countLit q [-2]) (countLit q [-6, -7]) (count1243 q) 2 (meaning1242 q) (meaning1244 q) hs
  change valuationOf q 1242 = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 1242 = false ∨ valuation q 1244 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1243 = true := by
  have hs : count1243 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1243)) (countLit q [-2]) (countLit q [-6, -7]) (count1243 q) 1 (meaningNeg2 q) (meaning1243 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1243 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1243 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1242 = false ∨ valuationOf q 1245 = true := by
  have hs : count1243 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1242)) (literal (valuationOf q) (1245)) (countLit q [-2]) (countLit q [-6, -7]) (count1243 q) 1 2 (meaningNeg2 q) (meaning1242 q) (meaning1245 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1242 = false ∨ valuationOf q 1245 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1242 = false ∨ valuation q 1245 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1246 = true := by
  have hs : count1246 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1246)) (countLit q [-11]) (countLit q [-13]) (count1246 q) 1 (meaningNeg13 q) (meaning1246 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1246 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1246 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1246 = true := by
  have hs : count1246 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1246)) (countLit q [-11]) (countLit q [-13]) (count1246 q) 1 (meaningNeg11 q) (meaning1246 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1246 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1246 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1247 = true := by
  have hs : count1246 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1247)) (countLit q [-11]) (countLit q [-13]) (count1246 q) 1 1 (meaningNeg11 q) (meaningNeg13 q) (meaning1247 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1247 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 13 = true ∨ valuation q 1247 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 1246 = false ∨ valuationOf q 1248 = true := by
  have hs : count1248 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_right (literal (valuationOf q) (1246)) (literal (valuationOf q) (1248)) (countLit q [-8]) (countLit q [-11, -13]) (count1248 q) 1 (meaning1246 q) (meaning1248 q) hs
  change valuationOf q 1246 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 1246 = false ∨ valuation q 1248 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 1247 = false ∨ valuationOf q 1249 = true := by
  have hs : count1248 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_right (literal (valuationOf q) (1247)) (literal (valuationOf q) (1249)) (countLit q [-8]) (countLit q [-11, -13]) (count1248 q) 2 (meaning1247 q) (meaning1249 q) hs
  change valuationOf q 1247 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 1247 = false ∨ valuation q 1249 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1248 = true := by
  have hs : count1248 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1248)) (countLit q [-8]) (countLit q [-11, -13]) (count1248 q) 1 (meaningNeg8 q) (meaning1248 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1248 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1246 = false ∨ valuationOf q 1249 = true := by
  have hs : count1248 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1246)) (literal (valuationOf q) (1249)) (countLit q [-8]) (countLit q [-11, -13]) (count1248 q) 1 1 (meaningNeg8 q) (meaning1246 q) (meaning1249 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1246 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1246 = false ∨ valuation q 1249 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1247 = false ∨ valuationOf q 1250 = true := by
  have hs : count1248 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1247)) (literal (valuationOf q) (1250)) (countLit q [-8]) (countLit q [-11, -13]) (count1248 q) 1 2 (meaningNeg8 q) (meaning1247 q) (meaning1250 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1247 = false ∨ valuationOf q 1250 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1247 = false ∨ valuation q 1250 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 1248 = false ∨ valuationOf q 1251 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_right (literal (valuationOf q) (1248)) (literal (valuationOf q) (1251)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1251 q) 1 (meaning1248 q) (meaning1251 q) hs
  change valuationOf q 1248 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 1248 = false ∨ valuation q 1251 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1252 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_right (literal (valuationOf q) (1249)) (literal (valuationOf q) (1252)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1251 q) 2 (meaning1249 q) (meaning1252 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1252 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 1250 = false ∨ valuationOf q 1253 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_right (literal (valuationOf q) (1250)) (literal (valuationOf q) (1253)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1251 q) 3 (meaning1250 q) (meaning1253 q) hs
  change valuationOf q 1250 = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 1250 = false ∨ valuation q 1253 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1251 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_left (literal (valuationOf q) (1243)) (literal (valuationOf q) (1251)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1251 q) 1 (meaning1243 q) (meaning1251 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1251 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1252 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1243)) (literal (valuationOf q) (1248)) (literal (valuationOf q) (1252)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1251 q) 1 1 (meaning1243 q) (meaning1248 q) (meaning1252 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1248 = false ∨ valuation q 1252 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1252 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -11, -13])
  have hm := merge_left (literal (valuationOf q) (1244)) (literal (valuationOf q) (1252)) (countLit q [-2, -6, -7]) (countLit q [-8, -11, -13]) (count1251 q) 2 (meaning1244 q) (meaning1252 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1252 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E175.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112175
