import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 900 = true := by
  have hs : count900 q = (countLit q [-71, -73, -75]) + (countLit q [-77, -79, -82, -83]) := List.countP_append (p := literal q) (l₁ := [-71, -73, -75]) (l₂ := [-77, -79, -82, -83])
  have hm := merge_right (literal (valuationOf q) (896)) (literal (valuationOf q) (900)) (countLit q [-71, -73, -75]) (countLit q [-77, -79, -82, -83]) (count900 q) 1 (meaning896 q) (meaning900 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 900 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 907 = true := by
  have hs : count907 q = (countLit q [-59, -60, -61, -64, -65, -66, -68]) + (countLit q [-71, -73, -75, -77, -79, -82, -83]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -61, -64, -65, -66, -68]) (l₂ := [-71, -73, -75, -77, -79, -82, -83])
  have hm := merge_right (literal (valuationOf q) (900)) (literal (valuationOf q) (907)) (countLit q [-59, -60, -61, -64, -65, -66, -68]) (countLit q [-71, -73, -75, -77, -79, -82, -83]) (count907 q) 1 (meaning900 q) (meaning907 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 907 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 921 = true := by
  have hs : count921 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (921)) (countLit q [-86]) (countLit q [-89]) (count921 q) 1 (meaningNeg89 q) (meaning921 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 921 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 921 = false ∨ valuationOf q 924 = true := by
  have hs : count923 q = (countLit q [-84]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (921)) (literal (valuationOf q) (924)) (countLit q [-84]) (countLit q [-86, -89]) (count923 q) 1 1 (meaningNeg84 q) (meaning921 q) (meaning924 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 921 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 921 = false ∨ valuation q 924 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 935 = true := by
  have hs : count934 q = (countLit q [-84, -86, -89]) + (countLit q [-91, -92, -94, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -86, -89]) (l₂ := [-91, -92, -94, -96])
  have hm := merge_left (literal (valuationOf q) (924)) (literal (valuationOf q) (935)) (countLit q [-84, -86, -89]) (countLit q [-91, -92, -94, -96]) (count934 q) 2 (meaning924 q) (meaning935 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 935 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 962 = true := by
  have hs : count961 q = (countLit q [-84, -86, -89, -91, -92, -94, -96]) + (countLit q [-99, -100, -102, -105, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-84, -86, -89, -91, -92, -94, -96]) (l₂ := [-99, -100, -102, -105, -107, -108, -110])
  have hm := merge_left (literal (valuationOf q) (935)) (literal (valuationOf q) (962)) (countLit q [-84, -86, -89, -91, -92, -94, -96]) (countLit q [-99, -100, -102, -105, -107, -108, -110]) (count961 q) 2 (meaning935 q) (meaning962 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 962 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 962 = false ∨ valuationOf q 977 = true := by
  have hs : count975 q = (countLit q [-59, -60, -61, -64, -65, -66, -68, -71, -73, -75, -77, -79, -82, -83]) + (countLit q [-84, -86, -89, -91, -92, -94, -96, -99, -100, -102, -105, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -61, -64, -65, -66, -68, -71, -73, -75, -77, -79, -82, -83]) (l₂ := [-84, -86, -89, -91, -92, -94, -96, -99, -100, -102, -105, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (962)) (literal (valuationOf q) (977)) (countLit q [-59, -60, -61, -64, -65, -66, -68, -71, -73, -75, -77, -79, -82, -83]) (countLit q [-84, -86, -89, -91, -92, -94, -96, -99, -100, -102, -105, -107, -108, -110]) (count975 q) 1 2 (meaning907 q) (meaning962 q) (meaning977 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 962 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 962 = false ∨ valuation q 977 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 977 = false ∨ valuationOf q 1004 = true := by
  have hs : count990 q = (countLit q [-1, -3, -4, -5, -7, -9, -11, -13, -15, -18, -20, -23, -26, -27, -28, -31, -34, -36, -37, -38, -41, -43, -44, -48, -49, -52, -56]) + (countLit q [-59, -60, -61, -64, -65, -66, -68, -71, -73, -75, -77, -79, -82, -83, -84, -86, -89, -91, -92, -94, -96, -99, -100, -102, -105, -107, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -11, -13, -15, -18, -20, -23, -26, -27, -28, -31, -34, -36, -37, -38, -41, -43, -44, -48, -49, -52, -56]) (l₂ := [-59, -60, -61, -64, -65, -66, -68, -71, -73, -75, -77, -79, -82, -83, -84, -86, -89, -91, -92, -94, -96, -99, -100, -102, -105, -107, -108, -110])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (977)) (literal (valuationOf q) (1004)) (countLit q [-1, -3, -4, -5, -7, -9, -11, -13, -15, -18, -20, -23, -26, -27, -28, -31, -34, -36, -37, -38, -41, -43, -44, -48, -49, -52, -56]) (countLit q [-59, -60, -61, -64, -65, -66, -68, -71, -73, -75, -77, -79, -82, -83, -84, -86, -89, -91, -92, -94, -96, -99, -100, -102, -105, -107, -108, -110]) (count990 q) 12 3 (meaning863 q) (meaning977 q) (meaning1004 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 977 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 977 = false ∨ valuation q 1004 = true := counterClause744 (baseVal q)

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false := by
  rw [value1004]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count990 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause746 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-6]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-8])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1319)) (countLit q [-6]) (countLit q [-8]) (count1319 q) 1 (meaningNeg6 q) (meaning1319 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1319 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1321 = true := by
  have hs : count1321 q = (countLit q [-2]) + (countLit q [-6, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -8])
  have hm := merge_right (literal (valuationOf q) (1319)) (literal (valuationOf q) (1321)) (countLit q [-2]) (countLit q [-6, -8]) (count1321 q) 1 (meaning1319 q) (meaning1321 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1321 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1321 = true := by
  have hs : count1321 q = (countLit q [-2]) + (countLit q [-6, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -8])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1321)) (countLit q [-2]) (countLit q [-6, -8]) (count1321 q) 1 (meaningNeg2 q) (meaning1321 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1321 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1319 = false ∨ valuationOf q 1322 = true := by
  have hs : count1321 q = (countLit q [-2]) + (countLit q [-6, -8]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -8])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1322)) (countLit q [-2]) (countLit q [-6, -8]) (count1321 q) 1 1 (meaningNeg2 q) (meaning1319 q) (meaning1322 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1319 = false ∨ valuation q 1322 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1324 = true := by
  have hs : count1324 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1324)) (countLit q [-10]) (countLit q [-12]) (count1324 q) 1 (meaningNeg12 q) (meaning1324 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1324 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-14]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16])
  have hm := merge_right (literal (valuationOf q) (-16)) (literal (valuationOf q) (1326)) (countLit q [-14]) (countLit q [-16]) (count1326 q) 1 (meaningNeg16 q) (meaning1326 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1326 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-14]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1326)) (countLit q [-14]) (countLit q [-16]) (count1326 q) 1 (meaningNeg14 q) (meaning1326 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1326 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 16 = true ∨ valuationOf q 1327 = true := by
  have hs : count1326 q = (countLit q [-14]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-16)) (literal (valuationOf q) (1327)) (countLit q [-14]) (countLit q [-16]) (count1326 q) 1 1 (meaningNeg14 q) (meaningNeg16 q) (meaning1327 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 16)) = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 16 = true ∨ valuation q 1327 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1328 = true := by
  have hs : count1328 q = (countLit q [-10, -12]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-10, -12]) (l₂ := [-14, -16])
  have hm := merge_right (literal (valuationOf q) (1326)) (literal (valuationOf q) (1328)) (countLit q [-10, -12]) (countLit q [-14, -16]) (count1328 q) 1 (meaning1326 q) (meaning1328 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1328 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1329 = true := by
  have hs : count1328 q = (countLit q [-10, -12]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-10, -12]) (l₂ := [-14, -16])
  have hm := merge_right (literal (valuationOf q) (1327)) (literal (valuationOf q) (1329)) (countLit q [-10, -12]) (countLit q [-14, -16]) (count1328 q) 2 (meaning1327 q) (meaning1329 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1329 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1328 = true := by
  have hs : count1328 q = (countLit q [-10, -12]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-10, -12]) (l₂ := [-14, -16])
  have hm := merge_left (literal (valuationOf q) (1324)) (literal (valuationOf q) (1328)) (countLit q [-10, -12]) (countLit q [-14, -16]) (count1328 q) 1 (meaning1324 q) (meaning1328 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1328 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1329 = true := by
  have hs : count1328 q = (countLit q [-10, -12]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-10, -12]) (l₂ := [-14, -16])
  have hm := merge_two (literal (valuationOf q) (1324)) (literal (valuationOf q) (1326)) (literal (valuationOf q) (1329)) (countLit q [-10, -12]) (countLit q [-14, -16]) (count1328 q) 1 1 (meaning1324 q) (meaning1326 q) (meaning1329 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1326 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1326 = false ∨ valuation q 1329 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1330 = true := by
  have hs : count1328 q = (countLit q [-10, -12]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-10, -12]) (l₂ := [-14, -16])
  have hm := merge_two (literal (valuationOf q) (1324)) (literal (valuationOf q) (1327)) (literal (valuationOf q) (1330)) (countLit q [-10, -12]) (countLit q [-14, -16]) (count1328 q) 1 2 (meaning1324 q) (meaning1327 q) (meaning1330 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1327 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1327 = false ∨ valuation q 1330 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1332 = true := by
  have hs : count1332 q = (countLit q [-2, -6, -8]) + (countLit q [-10, -12, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8]) (l₂ := [-10, -12, -14, -16])
  have hm := merge_right (literal (valuationOf q) (1328)) (literal (valuationOf q) (1332)) (countLit q [-2, -6, -8]) (countLit q [-10, -12, -14, -16]) (count1332 q) 1 (meaning1328 q) (meaning1332 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1332 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1333 = true := by
  have hs : count1332 q = (countLit q [-2, -6, -8]) + (countLit q [-10, -12, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8]) (l₂ := [-10, -12, -14, -16])
  have hm := merge_right (literal (valuationOf q) (1329)) (literal (valuationOf q) (1333)) (countLit q [-2, -6, -8]) (countLit q [-10, -12, -14, -16]) (count1332 q) 2 (meaning1329 q) (meaning1333 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1333 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1334 = true := by
  have hs : count1332 q = (countLit q [-2, -6, -8]) + (countLit q [-10, -12, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8]) (l₂ := [-10, -12, -14, -16])
  have hm := merge_right (literal (valuationOf q) (1330)) (literal (valuationOf q) (1334)) (countLit q [-2, -6, -8]) (countLit q [-10, -12, -14, -16]) (count1332 q) 3 (meaning1330 q) (meaning1334 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1334 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 1321 = false ∨ valuationOf q 1332 = true := by
  have hs : count1332 q = (countLit q [-2, -6, -8]) + (countLit q [-10, -12, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8]) (l₂ := [-10, -12, -14, -16])
  have hm := merge_left (literal (valuationOf q) (1321)) (literal (valuationOf q) (1332)) (countLit q [-2, -6, -8]) (countLit q [-10, -12, -14, -16]) (count1332 q) 1 (meaning1321 q) (meaning1332 q) hs
  change valuationOf q 1321 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 1321 = false ∨ valuation q 1332 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 1321 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1333 = true := by
  have hs : count1332 q = (countLit q [-2, -6, -8]) + (countLit q [-10, -12, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8]) (l₂ := [-10, -12, -14, -16])
  have hm := merge_two (literal (valuationOf q) (1321)) (literal (valuationOf q) (1328)) (literal (valuationOf q) (1333)) (countLit q [-2, -6, -8]) (countLit q [-10, -12, -14, -16]) (count1332 q) 1 1 (meaning1321 q) (meaning1328 q) (meaning1333 q) hs
  change valuationOf q 1321 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 1321 = false ∨ valuation q 1328 = false ∨ valuation q 1333 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1321 = false ∨ valuationOf q 1329 = false ∨ valuationOf q 1334 = true := by
  have hs : count1332 q = (countLit q [-2, -6, -8]) + (countLit q [-10, -12, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8]) (l₂ := [-10, -12, -14, -16])
  have hm := merge_two (literal (valuationOf q) (1321)) (literal (valuationOf q) (1329)) (literal (valuationOf q) (1334)) (countLit q [-2, -6, -8]) (countLit q [-10, -12, -14, -16]) (count1332 q) 1 2 (meaning1321 q) (meaning1329 q) (meaning1334 q) hs
  change valuationOf q 1321 = false ∨ valuationOf q 1329 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1321 = false ∨ valuation q 1329 = false ∨ valuation q 1334 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 1321 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1335 = true := by
  have hs : count1332 q = (countLit q [-2, -6, -8]) + (countLit q [-10, -12, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8]) (l₂ := [-10, -12, -14, -16])
  have hm := merge_two (literal (valuationOf q) (1321)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1335)) (countLit q [-2, -6, -8]) (countLit q [-10, -12, -14, -16]) (count1332 q) 1 3 (meaning1321 q) (meaning1330 q) (meaning1335 q) hs
  change valuationOf q 1321 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 1321 = false ∨ valuation q 1330 = false ∨ valuation q 1335 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1334 = true := by
  have hs : count1332 q = (countLit q [-2, -6, -8]) + (countLit q [-10, -12, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8]) (l₂ := [-10, -12, -14, -16])
  have hm := merge_two (literal (valuationOf q) (1322)) (literal (valuationOf q) (1328)) (literal (valuationOf q) (1334)) (countLit q [-2, -6, -8]) (countLit q [-10, -12, -14, -16]) (count1332 q) 2 1 (meaning1322 q) (meaning1328 q) (meaning1334 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1328 = false ∨ valuation q 1334 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1339 = true := by
  have hs : count1339 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1339)) (countLit q [-19]) (countLit q [-21]) (count1339 q) 1 (meaningNeg21 q) (meaning1339 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1339 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1339 = true := by
  have hs : count1339 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1339)) (countLit q [-19]) (countLit q [-21]) (count1339 q) 1 (meaningNeg19 q) (meaning1339 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1339 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E161.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112161
