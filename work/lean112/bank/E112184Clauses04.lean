import E112184Semantics
import B112E184Inputs
namespace Snake9.Regrowth.E112184
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause129 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-77, -78, -82, -84, -87, -89]) + (countLit q [-90, -92, -96, -97, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -82, -84, -87, -89]) (l₂ := [-90, -92, -96, -97, -98, -99])
  have hm := merge_right (literal (valuationOf q) (1357)) (literal (valuationOf q) (1363)) (countLit q [-77, -78, -82, -84, -87, -89]) (countLit q [-90, -92, -96, -97, -98, -99]) (count1362 q) 2 (meaning1357 q) (meaning1363 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1363 = true := counterClause129 (baseVal q)

theorem counterClause130 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-77, -78, -82, -84, -87, -89]) + (countLit q [-90, -92, -96, -97, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -82, -84, -87, -89]) (l₂ := [-90, -92, -96, -97, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1340)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1363)) (countLit q [-77, -78, -82, -84, -87, -89]) (countLit q [-90, -92, -96, -97, -98, -99]) (count1362 q) 1 1 (meaning1340 q) (meaning1356 q) (meaning1363 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1356 = false ∨ valuation q 1363 = true := counterClause130 (baseVal q)

theorem counterClause131 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-77, -78, -82, -84, -87, -89]) + (countLit q [-90, -92, -96, -97, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -82, -84, -87, -89]) (l₂ := [-90, -92, -96, -97, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1340)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1364)) (countLit q [-77, -78, -82, -84, -87, -89]) (countLit q [-90, -92, -96, -97, -98, -99]) (count1362 q) 1 2 (meaning1340 q) (meaning1357 q) (meaning1364 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1357 = false ∨ valuation q 1364 = true := counterClause131 (baseVal q)

theorem counterClause132 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-77, -78, -82, -84, -87, -89]) + (countLit q [-90, -92, -96, -97, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -82, -84, -87, -89]) (l₂ := [-90, -92, -96, -97, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1364)) (countLit q [-77, -78, -82, -84, -87, -89]) (countLit q [-90, -92, -96, -97, -98, -99]) (count1362 q) 2 1 (meaning1341 q) (meaning1356 q) (meaning1364 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1356 = false ∨ valuation q 1364 = true := counterClause132 (baseVal q)

theorem counterClause133 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1374 = true := by
  have hs : count1370 q = (countLit q [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76]) + (countLit q [-77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76]) (l₂ := [-77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1323)) (literal (valuationOf q) (1364)) (literal (valuationOf q) (1374)) (countLit q [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76]) (countLit q [-77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99]) (count1370 q) 2 3 (meaning1323 q) (meaning1364 q) (meaning1374 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1364 = false ∨ valuation q 1374 = true := counterClause133 (baseVal q)

theorem counterClause134 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1374 = true := by
  have hs : count1370 q = (countLit q [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76]) + (countLit q [-77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76]) (l₂ := [-77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1324)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1374)) (countLit q [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76]) (countLit q [-77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99]) (count1370 q) 3 2 (meaning1324 q) (meaning1363 q) (meaning1374 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1363 = false ∨ valuation q 1374 = true := counterClause134 (baseVal q)

theorem counterClause135 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1375 = true := by
  have hs : count1370 q = (countLit q [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76]) + (countLit q [-77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76]) (l₂ := [-77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1324)) (literal (valuationOf q) (1364)) (literal (valuationOf q) (1375)) (countLit q [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76]) (countLit q [-77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99]) (count1370 q) 3 3 (meaning1324 q) (meaning1364 q) (meaning1375 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1364 = false ∨ valuation q 1375 = true := counterClause135 (baseVal q)

theorem counterClause136 (q : Nat → Bool) : valuationOf q 1325 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1374 = true := by
  have hs : count1370 q = (countLit q [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76]) + (countLit q [-77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76]) (l₂ := [-77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1325)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1374)) (countLit q [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76]) (countLit q [-77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99]) (count1370 q) 4 1 (meaning1325 q) (meaning1362 q) (meaning1374 q) hs
  change valuationOf q 1325 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 1325 = false ∨ valuation q 1362 = false ∨ valuation q 1374 = true := counterClause136 (baseVal q)

theorem counterClause137 (q : Nat → Bool) : valuationOf q 1283 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1385 = true := by
  have hs : count1378 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28, -31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52]) + (countLit q [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76, -77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28, -31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52]) (l₂ := [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76, -77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1283)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1385)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28, -31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52]) (countLit q [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76, -77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99]) (count1378 q) 2 6 (meaning1283 q) (meaning1375 q) (meaning1385 q) hs
  change valuationOf q 1283 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 1283 = false ∨ valuation q 1375 = false ∨ valuation q 1385 = true := counterClause137 (baseVal q)

theorem counterClause138 (q : Nat → Bool) : valuationOf q 1284 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1385 = true := by
  have hs : count1378 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28, -31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52]) + (countLit q [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76, -77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28, -31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52]) (l₂ := [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76, -77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1284)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1385)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -22, -23, -24, -26, -28, -31, -34, -35, -36, -38, -42, -43, -44, -45, -49, -51, -52]) (countLit q [-54, -58, -59, -60, -61, -65, -66, -69, -70, -72, -74, -76, -77, -78, -82, -84, -87, -89, -90, -92, -96, -97, -98, -99]) (count1378 q) 3 5 (meaning1284 q) (meaning1374 q) (meaning1385 q) hs
  change valuationOf q 1284 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 1284 = false ∨ valuation q 1374 = false ∨ valuation q 1385 = true := counterClause138 (baseVal q)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false := by
  rw [value1385]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1378 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem block4 (q : Snake 81) (h : Conditions q) : B112E184.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h⟩

end
end Snake9.Regrowth.E112184
