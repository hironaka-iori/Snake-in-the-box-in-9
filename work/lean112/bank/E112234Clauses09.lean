import E112234Semantics
import B112E234Inputs
namespace Snake9.Regrowth.E112234
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1390 = true := by
  have hs : count1385 q = (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) + (countLit q [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) (l₂ := [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1390)) (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]) (countLit q [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) (count1385 q) 3 3 (meaning1329 q) (meaning1376 q) (meaning1390 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1376 = false ∨ valuation q 1390 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 1284 = false ∨ valuationOf q 1390 = false ∨ valuationOf q 1406 = true := by
  have hs : count1396 q = (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) + (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76, -77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (l₂ := [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76, -77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (1284)) (literal (valuationOf q) (1390)) (literal (valuationOf q) (1406)) (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76, -77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) (count1396 q) 5 6 (meaning1284 q) (meaning1390 q) (meaning1406 q) hs
  change valuationOf q 1284 = false ∨ valuationOf q 1390 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 1284 = false ∨ valuation q 1390 = false ∨ valuation q 1406 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1406 = true := by
  have hs : count1396 q = (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) + (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76, -77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (l₂ := [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76, -77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (1285)) (literal (valuationOf q) (1389)) (literal (valuationOf q) (1406)) (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76, -77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) (count1396 q) 6 5 (meaning1285 q) (meaning1389 q) (meaning1406 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1389 = false ∨ valuation q 1406 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 1286 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1406 = true := by
  have hs : count1396 q = (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) + (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76, -77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (l₂ := [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76, -77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101])
  have hm := merge_two (literal (valuationOf q) (1286)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1406)) (countLit q [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]) (countLit q [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76, -77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]) (count1396 q) 7 4 (meaning1286 q) (meaning1388 q) (meaning1406 q) hs
  change valuationOf q 1286 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 1286 = false ∨ valuation q 1388 = false ∨ valuation q 1406 = true := counterClause292 (baseVal q)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false := by
  rw [value1406]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1396 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 11 = false ∨ valuation q 17 = false ∨ valuation q 19 = false := by
  rw [value9, value11, value17, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (163 : Vertex) (177 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 23 = false ∨ valuation q 25 = false := by
  rw [value14, value15, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (173 : Vertex) (175 : Vertex) (189 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 19 = false := by
  rw [value16, value17, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value22, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (188 : Vertex) (189 : Vertex) (190 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 34 = false ∨ valuation q 35 = false := by
  rw [value28, value29, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (229 : Vertex) (244 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E234.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h⟩

end
end Snake9.Regrowth.E112234
