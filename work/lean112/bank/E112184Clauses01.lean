import E112184Semantics
import B112E184Inputs
namespace Snake9.Regrowth.E112184
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 123 = false := by
  rw [value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (137 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 127 = false := by
  rw [value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (148 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 132 = false := by
  rw [value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (155 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 136 = false := by
  rw [value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (199 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 144 = false := by
  rw [value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (214 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 153 = false := by
  rw [value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (296 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 162 = false := by
  rw [value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (316 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 171 = false := by
  rw [value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (346 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 177 = false := by
  rw [value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (406 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 178 = false := by
  rw [value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (410 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 185 = false := by
  rw [value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (428 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 190 = false := by
  rw [value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (487 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 200 = false := by
  rw [value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (508 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause46 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1202 = true := by
  have hs : count1202 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1202)) (countLit q [-6]) (countLit q [-7]) (count1202 q) 1 (meaningNeg6 q) (meaning1202 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1202 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1202 = true := counterClause46 (baseVal q)

theorem counterClause47 (q : Nat → Bool) : valuationOf q 1202 = false ∨ valuationOf q 1204 = true := by
  have hs : count1204 q = (countLit q [-5]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-6, -7])
  have hm := merge_right (literal (valuationOf q) (1202)) (literal (valuationOf q) (1204)) (countLit q [-5]) (countLit q [-6, -7]) (count1204 q) 1 (meaning1202 q) (meaning1204 q) hs
  change valuationOf q 1202 = false ∨ valuationOf q 1204 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 1202 = false ∨ valuation q 1204 = true := counterClause47 (baseVal q)

theorem counterClause48 (q : Nat → Bool) : valuationOf q 1204 = false ∨ valuationOf q 1212 = true := by
  have hs : count1212 q = (countLit q [-5, -6, -7]) + (countLit q [-9, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7]) (l₂ := [-9, -11, -14])
  have hm := merge_left (literal (valuationOf q) (1204)) (literal (valuationOf q) (1212)) (countLit q [-5, -6, -7]) (countLit q [-9, -11, -14]) (count1212 q) 1 (meaning1204 q) (meaning1212 q) hs
  change valuationOf q 1204 = false ∨ valuationOf q 1212 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 1204 = false ∨ valuation q 1212 = true := counterClause48 (baseVal q)

theorem counterClause49 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1218 = true := by
  have hs : count1218 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1218)) (countLit q [-22]) (countLit q [-23]) (count1218 q) 1 (meaningNeg23 q) (meaning1218 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1218 = true := counterClause49 (baseVal q)

theorem counterClause50 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1218 = true := by
  have hs : count1218 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1218)) (countLit q [-22]) (countLit q [-23]) (count1218 q) 1 (meaningNeg22 q) (meaning1218 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1218 = true := counterClause50 (baseVal q)

theorem counterClause51 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1220 = true := by
  have hs : count1220 q = (countLit q [-17]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-22, -23])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1220)) (countLit q [-17]) (countLit q [-22, -23]) (count1220 q) 1 (meaningNeg17 q) (meaning1220 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1220 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1220 = true := counterClause51 (baseVal q)

theorem counterClause52 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1218 = false ∨ valuationOf q 1221 = true := by
  have hs : count1220 q = (countLit q [-17]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-22, -23])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (1218)) (literal (valuationOf q) (1221)) (countLit q [-17]) (countLit q [-22, -23]) (count1220 q) 1 1 (meaningNeg17 q) (meaning1218 q) (meaning1221 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1221 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1218 = false ∨ valuation q 1221 = true := counterClause52 (baseVal q)

theorem counterClause53 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1223 = true := by
  have hs : count1223 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_right (literal (valuationOf q) (-28)) (literal (valuationOf q) (1223)) (countLit q [-26]) (countLit q [-28]) (count1223 q) 1 (meaningNeg28 q) (meaning1223 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1223 = true := counterClause53 (baseVal q)

theorem counterClause54 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1223 = true := by
  have hs : count1223 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1223)) (countLit q [-26]) (countLit q [-28]) (count1223 q) 1 (meaningNeg26 q) (meaning1223 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1223 = true := counterClause54 (baseVal q)

theorem counterClause55 (q : Nat → Bool) : valuationOf q 1223 = false ∨ valuationOf q 1225 = true := by
  have hs : count1225 q = (countLit q [-24]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26, -28])
  have hm := merge_right (literal (valuationOf q) (1223)) (literal (valuationOf q) (1225)) (countLit q [-24]) (countLit q [-26, -28]) (count1225 q) 1 (meaning1223 q) (meaning1225 q) hs
  change valuationOf q 1223 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 1223 = false ∨ valuation q 1225 = true := counterClause55 (baseVal q)

theorem counterClause56 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1225 = true := by
  have hs : count1225 q = (countLit q [-24]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26, -28])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1225)) (countLit q [-24]) (countLit q [-26, -28]) (count1225 q) 1 (meaningNeg24 q) (meaning1225 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1225 = true := counterClause56 (baseVal q)

theorem counterClause57 (q : Nat → Bool) : valuationOf q 1220 = false ∨ valuationOf q 1228 = true := by
  have hs : count1228 q = (countLit q [-17, -22, -23]) + (countLit q [-24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-17, -22, -23]) (l₂ := [-24, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1220)) (literal (valuationOf q) (1228)) (countLit q [-17, -22, -23]) (countLit q [-24, -26, -28]) (count1228 q) 1 (meaning1220 q) (meaning1228 q) hs
  change valuationOf q 1220 = false ∨ valuationOf q 1228 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 1220 = false ∨ valuation q 1228 = true := counterClause57 (baseVal q)

theorem counterClause58 (q : Nat → Bool) : valuationOf q 1220 = false ∨ valuationOf q 1225 = false ∨ valuationOf q 1229 = true := by
  have hs : count1228 q = (countLit q [-17, -22, -23]) + (countLit q [-24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-17, -22, -23]) (l₂ := [-24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1220)) (literal (valuationOf q) (1225)) (literal (valuationOf q) (1229)) (countLit q [-17, -22, -23]) (countLit q [-24, -26, -28]) (count1228 q) 1 1 (meaning1220 q) (meaning1225 q) (meaning1229 q) hs
  change valuationOf q 1220 = false ∨ valuationOf q 1225 = false ∨ valuationOf q 1229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 1220 = false ∨ valuation q 1225 = false ∨ valuation q 1229 = true := counterClause58 (baseVal q)

theorem counterClause59 (q : Nat → Bool) : valuationOf q 1221 = false ∨ valuationOf q 1229 = true := by
  have hs : count1228 q = (countLit q [-17, -22, -23]) + (countLit q [-24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-17, -22, -23]) (l₂ := [-24, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1221)) (literal (valuationOf q) (1229)) (countLit q [-17, -22, -23]) (countLit q [-24, -26, -28]) (count1228 q) 2 (meaning1221 q) (meaning1229 q) hs
  change valuationOf q 1221 = false ∨ valuationOf q 1229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 1221 = false ∨ valuation q 1229 = true := counterClause59 (baseVal q)

theorem counterClause60 (q : Nat → Bool) : valuationOf q 1228 = false ∨ valuationOf q 1234 = true := by
  have hs : count1234 q = (countLit q [-5, -6, -7, -9, -11, -14]) + (countLit q [-17, -22, -23, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14]) (l₂ := [-17, -22, -23, -24, -26, -28])
  have hm := merge_right (literal (valuationOf q) (1228)) (literal (valuationOf q) (1234)) (countLit q [-5, -6, -7, -9, -11, -14]) (countLit q [-17, -22, -23, -24, -26, -28]) (count1234 q) 1 (meaning1228 q) (meaning1234 q) hs
  change valuationOf q 1228 = false ∨ valuationOf q 1234 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 1228 = false ∨ valuation q 1234 = true := counterClause60 (baseVal q)

theorem counterClause61 (q : Nat → Bool) : valuationOf q 1229 = false ∨ valuationOf q 1235 = true := by
  have hs : count1234 q = (countLit q [-5, -6, -7, -9, -11, -14]) + (countLit q [-17, -22, -23, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14]) (l₂ := [-17, -22, -23, -24, -26, -28])
  have hm := merge_right (literal (valuationOf q) (1229)) (literal (valuationOf q) (1235)) (countLit q [-5, -6, -7, -9, -11, -14]) (countLit q [-17, -22, -23, -24, -26, -28]) (count1234 q) 2 (meaning1229 q) (meaning1235 q) hs
  change valuationOf q 1229 = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 1229 = false ∨ valuation q 1235 = true := counterClause61 (baseVal q)

theorem counterClause62 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1228 = false ∨ valuationOf q 1235 = true := by
  have hs : count1234 q = (countLit q [-5, -6, -7, -9, -11, -14]) + (countLit q [-17, -22, -23, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14]) (l₂ := [-17, -22, -23, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1212)) (literal (valuationOf q) (1228)) (literal (valuationOf q) (1235)) (countLit q [-5, -6, -7, -9, -11, -14]) (countLit q [-17, -22, -23, -24, -26, -28]) (count1234 q) 1 1 (meaning1212 q) (meaning1228 q) (meaning1235 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1228 = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1228 = false ∨ valuation q 1235 = true := counterClause62 (baseVal q)

theorem counterClause63 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1242 = true := by
  have hs : count1242 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1242)) (countLit q [-34]) (countLit q [-35]) (count1242 q) 1 (meaningNeg35 q) (meaning1242 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1242 = true := counterClause63 (baseVal q)

theorem counterClause64 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1242 = true := by
  have hs : count1242 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1242)) (countLit q [-34]) (countLit q [-35]) (count1242 q) 1 (meaningNeg34 q) (meaning1242 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1242 = true := counterClause64 (baseVal q)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E184.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112184
