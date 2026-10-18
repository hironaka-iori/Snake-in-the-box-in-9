import E112098Semantics
import B112E098Inputs
namespace Snake9.Regrowth.E112098
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 141 = false := by
  rw [value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (242 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 143 = false := by
  rw [value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (244 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 147 = false := by
  rw [value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (253 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 164 = false := by
  rw [value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (370 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 172 = false := by
  rw [value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (386 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 174 = false := by
  rw [value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (391 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 183 = false := by
  rw [value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (403 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 185 = false := by
  rw [value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (410 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 186 = false := by
  rw [value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (412 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 190 = false := by
  rw [value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (453 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 196 = false := by
  rw [value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (468 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 200 = false := by
  rw [value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (482 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause77 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1169 = true := by
  have hs : count1169 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (1169)) (countLit q [-4]) (countLit q [-6]) (count1169 q) 1 (meaningNeg6 q) (meaning1169 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1169 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1169 = true := counterClause77 (baseVal q)

theorem counterClause78 (q : Nat → Bool) : valuationOf q 1169 = false ∨ valuationOf q 1171 = true := by
  have hs : count1171 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_right (literal (valuationOf q) (1169)) (literal (valuationOf q) (1171)) (countLit q [-3]) (countLit q [-4, -6]) (count1171 q) 1 (meaning1169 q) (meaning1171 q) hs
  change valuationOf q 1169 = false ∨ valuationOf q 1171 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 1169 = false ∨ valuation q 1171 = true := counterClause78 (baseVal q)

theorem counterClause79 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1169 = false ∨ valuationOf q 1172 = true := by
  have hs : count1171 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1169)) (literal (valuationOf q) (1172)) (countLit q [-3]) (countLit q [-4, -6]) (count1171 q) 1 1 (meaningNeg3 q) (meaning1169 q) (meaning1172 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1169 = false ∨ valuationOf q 1172 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1169 = false ∨ valuation q 1172 = true := counterClause79 (baseVal q)

theorem counterClause80 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1174 = true := by
  have hs : count1174 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (1174)) (countLit q [-9]) (countLit q [-11]) (count1174 q) 1 (meaningNeg11 q) (meaning1174 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1174 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1174 = true := counterClause80 (baseVal q)

theorem counterClause81 (q : Nat → Bool) : valuationOf q 1174 = false ∨ valuationOf q 1176 = true := by
  have hs : count1176 q = (countLit q [-7]) + (countLit q [-9, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-9, -11])
  have hm := merge_right (literal (valuationOf q) (1174)) (literal (valuationOf q) (1176)) (countLit q [-7]) (countLit q [-9, -11]) (count1176 q) 1 (meaning1174 q) (meaning1176 q) hs
  change valuationOf q 1174 = false ∨ valuationOf q 1176 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 1174 = false ∨ valuation q 1176 = true := counterClause81 (baseVal q)

theorem counterClause82 (q : Nat → Bool) : valuationOf q 1171 = false ∨ valuationOf q 1176 = false ∨ valuationOf q 1180 = true := by
  have hs : count1179 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -11])
  have hm := merge_two (literal (valuationOf q) (1171)) (literal (valuationOf q) (1176)) (literal (valuationOf q) (1180)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -11]) (count1179 q) 1 1 (meaning1171 q) (meaning1176 q) (meaning1180 q) hs
  change valuationOf q 1171 = false ∨ valuationOf q 1176 = false ∨ valuationOf q 1180 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 1171 = false ∨ valuation q 1176 = false ∨ valuation q 1180 = true := counterClause82 (baseVal q)

theorem counterClause83 (q : Nat → Bool) : valuationOf q 1172 = false ∨ valuationOf q 1180 = true := by
  have hs : count1179 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -11]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -11])
  have hm := merge_left (literal (valuationOf q) (1172)) (literal (valuationOf q) (1180)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -11]) (count1179 q) 2 (meaning1172 q) (meaning1180 q) hs
  change valuationOf q 1172 = false ∨ valuationOf q 1180 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 1172 = false ∨ valuation q 1180 = true := counterClause83 (baseVal q)

theorem counterClause84 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1185 = true := by
  have hs : count1185 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1185)) (countLit q [-15]) (countLit q [-18]) (count1185 q) 1 (meaningNeg18 q) (meaning1185 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1185 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1185 = true := counterClause84 (baseVal q)

theorem counterClause85 (q : Nat → Bool) : valuationOf q 1185 = false ∨ valuationOf q 1187 = true := by
  have hs : count1187 q = (countLit q [-14]) + (countLit q [-15, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -18])
  have hm := merge_right (literal (valuationOf q) (1185)) (literal (valuationOf q) (1187)) (countLit q [-14]) (countLit q [-15, -18]) (count1187 q) 1 (meaning1185 q) (meaning1187 q) hs
  change valuationOf q 1185 = false ∨ valuationOf q 1187 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 1185 = false ∨ valuation q 1187 = true := counterClause85 (baseVal q)

theorem counterClause86 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1190 = true := by
  have hs : count1190 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1190)) (countLit q [-21]) (countLit q [-22]) (count1190 q) 1 (meaningNeg22 q) (meaning1190 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1190 = true := counterClause86 (baseVal q)

theorem counterClause87 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1190 = true := by
  have hs : count1190 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1190)) (countLit q [-21]) (countLit q [-22]) (count1190 q) 1 (meaningNeg21 q) (meaning1190 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1190 = true := counterClause87 (baseVal q)

theorem counterClause88 (q : Nat → Bool) : valuationOf q 1190 = false ∨ valuationOf q 1192 = true := by
  have hs : count1192 q = (countLit q [-19]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21, -22])
  have hm := merge_right (literal (valuationOf q) (1190)) (literal (valuationOf q) (1192)) (countLit q [-19]) (countLit q [-21, -22]) (count1192 q) 1 (meaning1190 q) (meaning1192 q) hs
  change valuationOf q 1190 = false ∨ valuationOf q 1192 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 1190 = false ∨ valuation q 1192 = true := counterClause88 (baseVal q)

theorem counterClause89 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1192 = true := by
  have hs : count1192 q = (countLit q [-19]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21, -22])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1192)) (countLit q [-19]) (countLit q [-21, -22]) (count1192 q) 1 (meaningNeg19 q) (meaning1192 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1192 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1192 = true := counterClause89 (baseVal q)

theorem counterClause90 (q : Nat → Bool) : valuationOf q 1192 = false ∨ valuationOf q 1195 = true := by
  have hs : count1195 q = (countLit q [-14, -15, -18]) + (countLit q [-19, -21, -22]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18]) (l₂ := [-19, -21, -22])
  have hm := merge_right (literal (valuationOf q) (1192)) (literal (valuationOf q) (1195)) (countLit q [-14, -15, -18]) (countLit q [-19, -21, -22]) (count1195 q) 1 (meaning1192 q) (meaning1195 q) hs
  change valuationOf q 1192 = false ∨ valuationOf q 1195 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 1192 = false ∨ valuation q 1195 = true := counterClause90 (baseVal q)

theorem counterClause91 (q : Nat → Bool) : valuationOf q 1187 = false ∨ valuationOf q 1195 = true := by
  have hs : count1195 q = (countLit q [-14, -15, -18]) + (countLit q [-19, -21, -22]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18]) (l₂ := [-19, -21, -22])
  have hm := merge_left (literal (valuationOf q) (1187)) (literal (valuationOf q) (1195)) (countLit q [-14, -15, -18]) (countLit q [-19, -21, -22]) (count1195 q) 1 (meaning1187 q) (meaning1195 q) hs
  change valuationOf q 1187 = false ∨ valuationOf q 1195 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 1187 = false ∨ valuation q 1195 = true := counterClause91 (baseVal q)

theorem counterClause92 (q : Nat → Bool) : valuationOf q 1187 = false ∨ valuationOf q 1192 = false ∨ valuationOf q 1196 = true := by
  have hs : count1195 q = (countLit q [-14, -15, -18]) + (countLit q [-19, -21, -22]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18]) (l₂ := [-19, -21, -22])
  have hm := merge_two (literal (valuationOf q) (1187)) (literal (valuationOf q) (1192)) (literal (valuationOf q) (1196)) (countLit q [-14, -15, -18]) (countLit q [-19, -21, -22]) (count1195 q) 1 1 (meaning1187 q) (meaning1192 q) (meaning1196 q) hs
  change valuationOf q 1187 = false ∨ valuationOf q 1192 = false ∨ valuationOf q 1196 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 1187 = false ∨ valuation q 1192 = false ∨ valuation q 1196 = true := counterClause92 (baseVal q)

theorem counterClause93 (q : Nat → Bool) : valuationOf q 1180 = false ∨ valuationOf q 1202 = true := by
  have hs : count1201 q = (countLit q [-3, -4, -6, -7, -9, -11]) + (countLit q [-14, -15, -18, -19, -21, -22]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -11]) (l₂ := [-14, -15, -18, -19, -21, -22])
  have hm := merge_left (literal (valuationOf q) (1180)) (literal (valuationOf q) (1202)) (countLit q [-3, -4, -6, -7, -9, -11]) (countLit q [-14, -15, -18, -19, -21, -22]) (count1201 q) 2 (meaning1180 q) (meaning1202 q) hs
  change valuationOf q 1180 = false ∨ valuationOf q 1202 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 1180 = false ∨ valuation q 1202 = true := counterClause93 (baseVal q)

theorem counterClause94 (q : Nat → Bool) : valuationOf q 1180 = false ∨ valuationOf q 1195 = false ∨ valuationOf q 1203 = true := by
  have hs : count1201 q = (countLit q [-3, -4, -6, -7, -9, -11]) + (countLit q [-14, -15, -18, -19, -21, -22]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -11]) (l₂ := [-14, -15, -18, -19, -21, -22])
  have hm := merge_two (literal (valuationOf q) (1180)) (literal (valuationOf q) (1195)) (literal (valuationOf q) (1203)) (countLit q [-3, -4, -6, -7, -9, -11]) (countLit q [-14, -15, -18, -19, -21, -22]) (count1201 q) 2 1 (meaning1180 q) (meaning1195 q) (meaning1203 q) hs
  change valuationOf q 1180 = false ∨ valuationOf q 1195 = false ∨ valuationOf q 1203 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 1180 = false ∨ valuation q 1195 = false ∨ valuation q 1203 = true := counterClause94 (baseVal q)

theorem counterClause95 (q : Nat → Bool) : valuationOf q 1180 = false ∨ valuationOf q 1196 = false ∨ valuationOf q 1204 = true := by
  have hs : count1201 q = (countLit q [-3, -4, -6, -7, -9, -11]) + (countLit q [-14, -15, -18, -19, -21, -22]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -11]) (l₂ := [-14, -15, -18, -19, -21, -22])
  have hm := merge_two (literal (valuationOf q) (1180)) (literal (valuationOf q) (1196)) (literal (valuationOf q) (1204)) (countLit q [-3, -4, -6, -7, -9, -11]) (countLit q [-14, -15, -18, -19, -21, -22]) (count1201 q) 2 2 (meaning1180 q) (meaning1196 q) (meaning1204 q) hs
  change valuationOf q 1180 = false ∨ valuationOf q 1196 = false ∨ valuationOf q 1204 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 1180 = false ∨ valuation q 1196 = false ∨ valuation q 1204 = true := counterClause95 (baseVal q)

theorem counterClause96 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1212 = true := by
  have hs : count1212 q = (countLit q [-26]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (1212)) (countLit q [-26]) (countLit q [-29]) (count1212 q) 1 (meaningNeg29 q) (meaning1212 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1212 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1212 = true := counterClause96 (baseVal q)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E098.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112098
