import E112118Semantics
import B112E118Inputs
namespace Snake9.Regrowth.E112118
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 140 = false := by
  rw [value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (296 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 152 = false := by
  rw [value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (327 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 162 = false := by
  rw [value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (346 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 171 = false := by
  rw [value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (406 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 172 = false := by
  rw [value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (410 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 179 = false := by
  rw [value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (428 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 184 = false := by
  rw [value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (487 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 194 = false := by
  rw [value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (508 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause41 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1152 = true := by
  have hs : count1152 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1152)) (countLit q [-12]) (countLit q [-13]) (count1152 q) 1 (meaningNeg13 q) (meaning1152 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1152 = true := counterClause41 (baseVal q)

theorem counterClause42 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1152 = true := by
  have hs : count1152 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-12)) (literal (valuationOf q) (1152)) (countLit q [-12]) (countLit q [-13]) (count1152 q) 1 (meaningNeg12 q) (meaning1152 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1152 = true := counterClause42 (baseVal q)

theorem counterClause43 (q : Nat → Bool) : valuationOf q 1152 = false ∨ valuationOf q 1154 = true := by
  have hs : count1154 q = (countLit q [-6]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1152)) (literal (valuationOf q) (1154)) (countLit q [-6]) (countLit q [-12, -13]) (count1154 q) 1 (meaning1152 q) (meaning1154 q) hs
  change valuationOf q 1152 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 1152 = false ∨ valuation q 1154 = true := counterClause43 (baseVal q)

theorem counterClause44 (q : Nat → Bool) : valuationOf q 1154 = false ∨ valuationOf q 1157 = true := by
  have hs : count1157 q = (countLit q [-3, -4]) + (countLit q [-6, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4]) (l₂ := [-6, -12, -13])
  have hm := merge_right (literal (valuationOf q) (1154)) (literal (valuationOf q) (1157)) (countLit q [-3, -4]) (countLit q [-6, -12, -13]) (count1157 q) 1 (meaning1154 q) (meaning1157 q) hs
  change valuationOf q 1154 = false ∨ valuationOf q 1157 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 1154 = false ∨ valuation q 1157 = true := counterClause44 (baseVal q)

theorem counterClause45 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1162 = true := by
  have hs : count1162 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1162)) (countLit q [-16]) (countLit q [-18]) (count1162 q) 1 (meaningNeg18 q) (meaning1162 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1162 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1162 = true := counterClause45 (baseVal q)

theorem counterClause46 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1162 = true := by
  have hs : count1162 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1162)) (countLit q [-16]) (countLit q [-18]) (count1162 q) 1 (meaningNeg16 q) (meaning1162 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1162 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1162 = true := counterClause46 (baseVal q)

theorem counterClause47 (q : Nat → Bool) : valuationOf q 1162 = false ∨ valuationOf q 1164 = true := by
  have hs : count1164 q = (countLit q [-14]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -18])
  have hm := merge_right (literal (valuationOf q) (1162)) (literal (valuationOf q) (1164)) (countLit q [-14]) (countLit q [-16, -18]) (count1164 q) 1 (meaning1162 q) (meaning1164 q) hs
  change valuationOf q 1162 = false ∨ valuationOf q 1164 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 1162 = false ∨ valuation q 1164 = true := counterClause47 (baseVal q)

theorem counterClause48 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1164 = true := by
  have hs : count1164 q = (countLit q [-14]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -18])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1164)) (countLit q [-14]) (countLit q [-16, -18]) (count1164 q) 1 (meaningNeg14 q) (meaning1164 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1164 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1164 = true := counterClause48 (baseVal q)

theorem counterClause49 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1167 = true := by
  have hs : count1167 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (1167)) (countLit q [-24]) (countLit q [-25]) (count1167 q) 1 (meaningNeg25 q) (meaning1167 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1167 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1167 = true := counterClause49 (baseVal q)

theorem counterClause50 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1167 = true := by
  have hs : count1167 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1167)) (countLit q [-24]) (countLit q [-25]) (count1167 q) 1 (meaningNeg24 q) (meaning1167 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1167 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1167 = true := counterClause50 (baseVal q)

theorem counterClause51 (q : Nat → Bool) : valuationOf q 1167 = false ∨ valuationOf q 1169 = true := by
  have hs : count1169 q = (countLit q [-21]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-24, -25])
  have hm := merge_right (literal (valuationOf q) (1167)) (literal (valuationOf q) (1169)) (countLit q [-21]) (countLit q [-24, -25]) (count1169 q) 1 (meaning1167 q) (meaning1169 q) hs
  change valuationOf q 1167 = false ∨ valuationOf q 1169 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 1167 = false ∨ valuation q 1169 = true := counterClause51 (baseVal q)

theorem counterClause52 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1169 = true := by
  have hs : count1169 q = (countLit q [-21]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-24, -25])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1169)) (countLit q [-21]) (countLit q [-24, -25]) (count1169 q) 1 (meaningNeg21 q) (meaning1169 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1169 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1169 = true := counterClause52 (baseVal q)

theorem counterClause53 (q : Nat → Bool) : valuationOf q 1169 = false ∨ valuationOf q 1172 = true := by
  have hs : count1172 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -24, -25])
  have hm := merge_right (literal (valuationOf q) (1169)) (literal (valuationOf q) (1172)) (countLit q [-14, -16, -18]) (countLit q [-21, -24, -25]) (count1172 q) 1 (meaning1169 q) (meaning1172 q) hs
  change valuationOf q 1169 = false ∨ valuationOf q 1172 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 1169 = false ∨ valuation q 1172 = true := counterClause53 (baseVal q)

theorem counterClause54 (q : Nat → Bool) : valuationOf q 1164 = false ∨ valuationOf q 1172 = true := by
  have hs : count1172 q = (countLit q [-14, -16, -18]) + (countLit q [-21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-21, -24, -25])
  have hm := merge_left (literal (valuationOf q) (1164)) (literal (valuationOf q) (1172)) (countLit q [-14, -16, -18]) (countLit q [-21, -24, -25]) (count1172 q) 1 (meaning1164 q) (meaning1172 q) hs
  change valuationOf q 1164 = false ∨ valuationOf q 1172 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 1164 = false ∨ valuation q 1172 = true := counterClause54 (baseVal q)

theorem counterClause55 (q : Nat → Bool) : valuationOf q 1172 = false ∨ valuationOf q 1178 = true := by
  have hs : count1178 q = (countLit q [-3, -4, -6, -12, -13]) + (countLit q [-14, -16, -18, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -12, -13]) (l₂ := [-14, -16, -18, -21, -24, -25])
  have hm := merge_right (literal (valuationOf q) (1172)) (literal (valuationOf q) (1178)) (countLit q [-3, -4, -6, -12, -13]) (countLit q [-14, -16, -18, -21, -24, -25]) (count1178 q) 1 (meaning1172 q) (meaning1178 q) hs
  change valuationOf q 1172 = false ∨ valuationOf q 1178 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 1172 = false ∨ valuation q 1178 = true := counterClause55 (baseVal q)

theorem counterClause56 (q : Nat → Bool) : valuationOf q 1157 = false ∨ valuationOf q 1178 = true := by
  have hs : count1178 q = (countLit q [-3, -4, -6, -12, -13]) + (countLit q [-14, -16, -18, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -12, -13]) (l₂ := [-14, -16, -18, -21, -24, -25])
  have hm := merge_left (literal (valuationOf q) (1157)) (literal (valuationOf q) (1178)) (countLit q [-3, -4, -6, -12, -13]) (countLit q [-14, -16, -18, -21, -24, -25]) (count1178 q) 1 (meaning1157 q) (meaning1178 q) hs
  change valuationOf q 1157 = false ∨ valuationOf q 1178 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 1157 = false ∨ valuation q 1178 = true := counterClause56 (baseVal q)

theorem counterClause57 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1185 = true := by
  have hs : count1185 q = (countLit q [-28]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-32])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1185)) (countLit q [-28]) (countLit q [-32]) (count1185 q) 1 (meaningNeg28 q) (meaning1185 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1185 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1185 = true := counterClause57 (baseVal q)

theorem counterClause58 (q : Nat → Bool) : valuationOf q 1185 = false ∨ valuationOf q 1187 = true := by
  have hs : count1187 q = (countLit q [-26]) + (countLit q [-28, -32]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28, -32])
  have hm := merge_right (literal (valuationOf q) (1185)) (literal (valuationOf q) (1187)) (countLit q [-26]) (countLit q [-28, -32]) (count1187 q) 1 (meaning1185 q) (meaning1187 q) hs
  change valuationOf q 1185 = false ∨ valuationOf q 1187 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 1185 = false ∨ valuation q 1187 = true := counterClause58 (baseVal q)

theorem counterClause59 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1187 = true := by
  have hs : count1187 q = (countLit q [-26]) + (countLit q [-28, -32]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28, -32])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1187)) (countLit q [-26]) (countLit q [-28, -32]) (count1187 q) 1 (meaningNeg26 q) (meaning1187 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1187 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1187 = true := counterClause59 (baseVal q)

theorem counterClause60 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1190 = true := by
  have hs : count1190 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1190)) (countLit q [-34]) (countLit q [-35]) (count1190 q) 1 (meaningNeg35 q) (meaning1190 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1190 = true := counterClause60 (baseVal q)

theorem counterClause61 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1190 = true := by
  have hs : count1190 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1190)) (countLit q [-34]) (countLit q [-35]) (count1190 q) 1 (meaningNeg34 q) (meaning1190 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1190 = true := counterClause61 (baseVal q)

theorem counterClause62 (q : Nat → Bool) : valuationOf q 1190 = false ∨ valuationOf q 1192 = true := by
  have hs : count1192 q = (countLit q [-33]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1190)) (literal (valuationOf q) (1192)) (countLit q [-33]) (countLit q [-34, -35]) (count1192 q) 1 (meaning1190 q) (meaning1192 q) hs
  change valuationOf q 1190 = false ∨ valuationOf q 1192 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 1190 = false ∨ valuation q 1192 = true := counterClause62 (baseVal q)

theorem counterClause63 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1192 = true := by
  have hs : count1192 q = (countLit q [-33]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -35])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1192)) (countLit q [-33]) (countLit q [-34, -35]) (count1192 q) 1 (meaningNeg33 q) (meaning1192 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1192 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1192 = true := counterClause63 (baseVal q)

theorem counterClause64 (q : Nat → Bool) : valuationOf q 1192 = false ∨ valuationOf q 1195 = true := by
  have hs : count1195 q = (countLit q [-26, -28, -32]) + (countLit q [-33, -34, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -32]) (l₂ := [-33, -34, -35])
  have hm := merge_right (literal (valuationOf q) (1192)) (literal (valuationOf q) (1195)) (countLit q [-26, -28, -32]) (countLit q [-33, -34, -35]) (count1195 q) 1 (meaning1192 q) (meaning1195 q) hs
  change valuationOf q 1192 = false ∨ valuationOf q 1195 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 1192 = false ∨ valuation q 1195 = true := counterClause64 (baseVal q)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E118.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112118
