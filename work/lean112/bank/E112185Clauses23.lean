import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1006 = true := by
  have hs : count991 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) + (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (l₂ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1006)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count991 q) 7 9 (meaning857 q) (meaning983 q) (meaning1006 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 983 = false ∨ valuation q 1006 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1006 = true := by
  have hs : count991 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) + (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (l₂ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1006)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count991 q) 8 8 (meaning858 q) (meaning982 q) (meaning1006 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 982 = false ∨ valuation q 1006 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1006 = true := by
  have hs : count991 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) + (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (l₂ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (859)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1006)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count991 q) 9 7 (meaning859 q) (meaning981 q) (meaning1006 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 981 = false ∨ valuation q 1006 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1006 = true := by
  have hs : count991 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) + (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (l₂ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (860)) (literal (valuationOf q) (980)) (literal (valuationOf q) (1006)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count991 q) 10 6 (meaning860 q) (meaning980 q) (meaning1006 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 980 = false ∨ valuation q 1006 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1006 = true := by
  have hs : count991 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) + (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (l₂ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (861)) (literal (valuationOf q) (979)) (literal (valuationOf q) (1006)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count991 q) 11 5 (meaning861 q) (meaning979 q) (meaning1006 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 979 = false ∨ valuation q 1006 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1006 = true := by
  have hs : count991 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) + (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (l₂ := [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (978)) (literal (valuationOf q) (1006)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (countLit q [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]) (count991 q) 12 4 (meaning862 q) (meaning978 q) (meaning1006 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 978 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 978 = false ∨ valuation q 1006 = true := counterClause742 (baseVal q)

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false := by
  rw [value1006]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count991 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause744 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1313 = true := by
  have hs : count1313 q = (countLit q [-16]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1313)) (countLit q [-16]) (countLit q [-19]) (count1313 q) 1 (meaningNeg19 q) (meaning1313 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1313 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1315 = true := by
  have hs : count1315 q = (countLit q [-14]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -19])
  have hm := merge_right (literal (valuationOf q) (1313)) (literal (valuationOf q) (1315)) (countLit q [-14]) (countLit q [-16, -19]) (count1315 q) 1 (meaning1313 q) (meaning1315 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1315 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1318 = true := by
  have hs : count1318 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1318)) (countLit q [-22]) (countLit q [-23]) (count1318 q) 1 (meaningNeg22 q) (meaning1318 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1318 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1320 = true := by
  have hs : count1320 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_right (literal (valuationOf q) (-28)) (literal (valuationOf q) (1320)) (countLit q [-26]) (countLit q [-28]) (count1320 q) 1 (meaningNeg28 q) (meaning1320 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1320 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1320 = true := by
  have hs : count1320 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1320)) (countLit q [-26]) (countLit q [-28]) (count1320 q) 1 (meaningNeg26 q) (meaning1320 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1320 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1322 = true := by
  have hs : count1322 q = (countLit q [-22, -23]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-26, -28])
  have hm := merge_right (literal (valuationOf q) (1320)) (literal (valuationOf q) (1322)) (countLit q [-22, -23]) (countLit q [-26, -28]) (count1322 q) 1 (meaning1320 q) (meaning1322 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1322 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 1318 = false ∨ valuationOf q 1322 = true := by
  have hs : count1322 q = (countLit q [-22, -23]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-26, -28])
  have hm := merge_left (literal (valuationOf q) (1318)) (literal (valuationOf q) (1322)) (countLit q [-22, -23]) (countLit q [-26, -28]) (count1322 q) 1 (meaning1318 q) (meaning1322 q) hs
  change valuationOf q 1318 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 1318 = false ∨ valuation q 1322 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 1315 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1327 = true := by
  have hs : count1326 q = (countLit q [-14, -16, -19]) + (countLit q [-22, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-22, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1315)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1327)) (countLit q [-14, -16, -19]) (countLit q [-22, -23, -26, -28]) (count1326 q) 1 1 (meaning1315 q) (meaning1322 q) (meaning1327 q) hs
  change valuationOf q 1315 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 1315 = false ∨ valuation q 1322 = false ∨ valuation q 1327 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1334 = true := by
  have hs : count1333 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -22, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -22, -23, -26, -28])
  have hm := merge_right (literal (valuationOf q) (1327)) (literal (valuationOf q) (1334)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -22, -23, -26, -28]) (count1333 q) 2 (meaning1327 q) (meaning1334 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1334 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1345 = true := by
  have hs : count1345 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1345)) (countLit q [-33]) (countLit q [-35]) (count1345 q) 1 (meaningNeg35 q) (meaning1345 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1345 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1347 = true := by
  have hs : count1347 q = (countLit q [-30]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33, -35])
  have hm := merge_right (literal (valuationOf q) (1345)) (literal (valuationOf q) (1347)) (countLit q [-30]) (countLit q [-33, -35]) (count1347 q) 1 (meaning1345 q) (meaning1347 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1347 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1350 = true := by
  have hs : count1350 q = (countLit q [-38]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1350)) (countLit q [-38]) (countLit q [-41]) (count1350 q) 1 (meaningNeg38 q) (meaning1350 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1350 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1352 = true := by
  have hs : count1352 q = (countLit q [-36]) + (countLit q [-38, -41]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38, -41])
  have hm := merge_right (literal (valuationOf q) (1350)) (literal (valuationOf q) (1352)) (countLit q [-36]) (countLit q [-38, -41]) (count1352 q) 1 (meaning1350 q) (meaning1352 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1352 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 1347 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1356 = true := by
  have hs : count1355 q = (countLit q [-30, -33, -35]) + (countLit q [-36, -38, -41]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35]) (l₂ := [-36, -38, -41])
  have hm := merge_two (literal (valuationOf q) (1347)) (literal (valuationOf q) (1352)) (literal (valuationOf q) (1356)) (countLit q [-30, -33, -35]) (countLit q [-36, -38, -41]) (count1355 q) 1 1 (meaning1347 q) (meaning1352 q) (meaning1356 q) hs
  change valuationOf q 1347 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 1347 = false ∨ valuation q 1352 = false ∨ valuation q 1356 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1361 = true := by
  have hs : count1361 q = (countLit q [-44]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1361)) (countLit q [-44]) (countLit q [-47]) (count1361 q) 1 (meaningNeg47 q) (meaning1361 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1361 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1363 = true := by
  have hs : count1363 q = (countLit q [-42]) + (countLit q [-44, -47]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44, -47])
  have hm := merge_right (literal (valuationOf q) (1361)) (literal (valuationOf q) (1363)) (countLit q [-42]) (countLit q [-44, -47]) (count1363 q) 1 (meaning1361 q) (meaning1363 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1363 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1368 = true := by
  have hs : count1368 q = (countLit q [-52]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (1368)) (countLit q [-52]) (countLit q [-55]) (count1368 q) 1 (meaningNeg55 q) (meaning1368 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1368 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 1368 = false ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-49, -50]) + (countLit q [-52, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-52, -55])
  have hm := merge_right (literal (valuationOf q) (1368)) (literal (valuationOf q) (1370)) (countLit q [-49, -50]) (countLit q [-52, -55]) (count1370 q) 1 (meaning1368 q) (meaning1370 q) hs
  change valuationOf q 1368 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 1368 = false ∨ valuation q 1370 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true := by
  have hs : count1374 q = (countLit q [-42, -44, -47]) + (countLit q [-49, -50, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -47]) (l₂ := [-49, -50, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1375)) (countLit q [-42, -44, -47]) (countLit q [-49, -50, -52, -55]) (count1374 q) 1 1 (meaning1363 q) (meaning1370 q) (meaning1375 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1370 = false ∨ valuation q 1375 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1384 = true := by
  have hs : count1381 q = (countLit q [-30, -33, -35, -36, -38, -41]) + (countLit q [-42, -44, -47, -49, -50, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -38, -41]) (l₂ := [-42, -44, -47, -49, -50, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1356)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1384)) (countLit q [-30, -33, -35, -36, -38, -41]) (countLit q [-42, -44, -47, -49, -50, -52, -55]) (count1381 q) 2 2 (meaning1356 q) (meaning1375 q) (meaning1384 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1375 = false ∨ valuation q 1384 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1398 = true := by
  have hs : count1393 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28]) + (countLit q [-30, -33, -35, -36, -38, -41, -42, -44, -47, -49, -50, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28]) (l₂ := [-30, -33, -35, -36, -38, -41, -42, -44, -47, -49, -50, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1334)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1398)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28]) (countLit q [-30, -33, -35, -36, -38, -41, -42, -44, -47, -49, -50, -52, -55]) (count1393 q) 2 4 (meaning1334 q) (meaning1384 q) (meaning1398 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1384 = false ∨ valuation q 1398 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1412 = true := by
  have hs : count1412 q = (countLit q [-63]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1412)) (countLit q [-63]) (countLit q [-65, -66]) (count1412 q) 1 (meaningNeg63 q) (meaning1412 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1412 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1415 = true := by
  have hs : count1415 q = (countLit q [-57, -58, -60]) + (countLit q [-63, -65, -66]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -60]) (l₂ := [-63, -65, -66])
  have hm := merge_right (literal (valuationOf q) (1412)) (literal (valuationOf q) (1415)) (countLit q [-57, -58, -60]) (countLit q [-63, -65, -66]) (count1415 q) 1 (meaning1412 q) (meaning1415 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1415 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-71]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (1421)) (countLit q [-71]) (countLit q [-72]) (count1421 q) 1 (meaningNeg72 q) (meaning1421 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1421 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-71]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1421)) (countLit q [-71]) (countLit q [-72]) (count1421 q) 1 (meaningNeg71 q) (meaning1421 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1421 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E185.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112185
