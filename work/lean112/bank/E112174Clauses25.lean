import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1231 = false ∨ valuationOf q 1233 = false ∨ valuationOf q 1236 = true := by
  have hs : count1235 q = (countLit q [-19, -20]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-19, -20]) (l₂ := [-23, -24])
  have hm := merge_two (literal (valuationOf q) (1231)) (literal (valuationOf q) (1233)) (literal (valuationOf q) (1236)) (countLit q [-19, -20]) (countLit q [-23, -24]) (count1235 q) 1 1 (meaning1231 q) (meaning1233 q) (meaning1236 q) hs
  change valuationOf q 1231 = false ∨ valuationOf q 1233 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1231 = false ∨ valuation q 1233 = false ∨ valuation q 1236 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1232 = false ∨ valuationOf q 1236 = true := by
  have hs : count1235 q = (countLit q [-19, -20]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-19, -20]) (l₂ := [-23, -24])
  have hm := merge_left (literal (valuationOf q) (1232)) (literal (valuationOf q) (1236)) (countLit q [-19, -20]) (countLit q [-23, -24]) (count1235 q) 2 (meaning1232 q) (meaning1236 q) hs
  change valuationOf q 1232 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1232 = false ∨ valuation q 1236 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1232 = false ∨ valuationOf q 1233 = false ∨ valuationOf q 1237 = true := by
  have hs : count1235 q = (countLit q [-19, -20]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-19, -20]) (l₂ := [-23, -24])
  have hm := merge_two (literal (valuationOf q) (1232)) (literal (valuationOf q) (1233)) (literal (valuationOf q) (1237)) (countLit q [-19, -20]) (countLit q [-23, -24]) (count1235 q) 2 1 (meaning1232 q) (meaning1233 q) (meaning1237 q) hs
  change valuationOf q 1232 = false ∨ valuationOf q 1233 = false ∨ valuationOf q 1237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1232 = false ∨ valuation q 1233 = false ∨ valuation q 1237 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1228 = false ∨ valuationOf q 1239 = true := by
  have hs : count1239 q = (countLit q [-11, -13, -15]) + (countLit q [-19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-11, -13, -15]) (l₂ := [-19, -20, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1228)) (literal (valuationOf q) (1239)) (countLit q [-11, -13, -15]) (countLit q [-19, -20, -23, -24]) (count1239 q) 1 (meaning1228 q) (meaning1239 q) hs
  change valuationOf q 1228 = false ∨ valuationOf q 1239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1228 = false ∨ valuation q 1239 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 1228 = false ∨ valuationOf q 1235 = false ∨ valuationOf q 1240 = true := by
  have hs : count1239 q = (countLit q [-11, -13, -15]) + (countLit q [-19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-11, -13, -15]) (l₂ := [-19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1228)) (literal (valuationOf q) (1235)) (literal (valuationOf q) (1240)) (countLit q [-11, -13, -15]) (countLit q [-19, -20, -23, -24]) (count1239 q) 1 1 (meaning1228 q) (meaning1235 q) (meaning1240 q) hs
  change valuationOf q 1228 = false ∨ valuationOf q 1235 = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 1228 = false ∨ valuation q 1235 = false ∨ valuation q 1240 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1228 = false ∨ valuationOf q 1236 = false ∨ valuationOf q 1241 = true := by
  have hs : count1239 q = (countLit q [-11, -13, -15]) + (countLit q [-19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-11, -13, -15]) (l₂ := [-19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1228)) (literal (valuationOf q) (1236)) (literal (valuationOf q) (1241)) (countLit q [-11, -13, -15]) (countLit q [-19, -20, -23, -24]) (count1239 q) 1 2 (meaning1228 q) (meaning1236 q) (meaning1241 q) hs
  change valuationOf q 1228 = false ∨ valuationOf q 1236 = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1228 = false ∨ valuation q 1236 = false ∨ valuation q 1241 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1228 = false ∨ valuationOf q 1237 = false ∨ valuationOf q 1242 = true := by
  have hs : count1239 q = (countLit q [-11, -13, -15]) + (countLit q [-19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-11, -13, -15]) (l₂ := [-19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1228)) (literal (valuationOf q) (1237)) (literal (valuationOf q) (1242)) (countLit q [-11, -13, -15]) (countLit q [-19, -20, -23, -24]) (count1239 q) 1 3 (meaning1228 q) (meaning1237 q) (meaning1242 q) hs
  change valuationOf q 1228 = false ∨ valuationOf q 1237 = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1228 = false ∨ valuation q 1237 = false ∨ valuation q 1242 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1229 = false ∨ valuationOf q 1240 = true := by
  have hs : count1239 q = (countLit q [-11, -13, -15]) + (countLit q [-19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-11, -13, -15]) (l₂ := [-19, -20, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1229)) (literal (valuationOf q) (1240)) (countLit q [-11, -13, -15]) (countLit q [-19, -20, -23, -24]) (count1239 q) 2 (meaning1229 q) (meaning1240 q) hs
  change valuationOf q 1229 = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1229 = false ∨ valuation q 1240 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1229 = false ∨ valuationOf q 1235 = false ∨ valuationOf q 1241 = true := by
  have hs : count1239 q = (countLit q [-11, -13, -15]) + (countLit q [-19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-11, -13, -15]) (l₂ := [-19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1229)) (literal (valuationOf q) (1235)) (literal (valuationOf q) (1241)) (countLit q [-11, -13, -15]) (countLit q [-19, -20, -23, -24]) (count1239 q) 2 1 (meaning1229 q) (meaning1235 q) (meaning1241 q) hs
  change valuationOf q 1229 = false ∨ valuationOf q 1235 = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1229 = false ∨ valuation q 1235 = false ∨ valuation q 1241 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1229 = false ∨ valuationOf q 1236 = false ∨ valuationOf q 1242 = true := by
  have hs : count1239 q = (countLit q [-11, -13, -15]) + (countLit q [-19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-11, -13, -15]) (l₂ := [-19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1229)) (literal (valuationOf q) (1236)) (literal (valuationOf q) (1242)) (countLit q [-11, -13, -15]) (countLit q [-19, -20, -23, -24]) (count1239 q) 2 2 (meaning1229 q) (meaning1236 q) (meaning1242 q) hs
  change valuationOf q 1229 = false ∨ valuationOf q 1236 = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1229 = false ∨ valuation q 1236 = false ∨ valuation q 1242 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1230 = false ∨ valuationOf q 1241 = true := by
  have hs : count1239 q = (countLit q [-11, -13, -15]) + (countLit q [-19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-11, -13, -15]) (l₂ := [-19, -20, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1230)) (literal (valuationOf q) (1241)) (countLit q [-11, -13, -15]) (countLit q [-19, -20, -23, -24]) (count1239 q) 3 (meaning1230 q) (meaning1241 q) hs
  change valuationOf q 1230 = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1230 = false ∨ valuation q 1241 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1230 = false ∨ valuationOf q 1235 = false ∨ valuationOf q 1242 = true := by
  have hs : count1239 q = (countLit q [-11, -13, -15]) + (countLit q [-19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-11, -13, -15]) (l₂ := [-19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1230)) (literal (valuationOf q) (1235)) (literal (valuationOf q) (1242)) (countLit q [-11, -13, -15]) (countLit q [-19, -20, -23, -24]) (count1239 q) 3 1 (meaning1230 q) (meaning1235 q) (meaning1242 q) hs
  change valuationOf q 1230 = false ∨ valuationOf q 1235 = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1230 = false ∨ valuation q 1235 = false ∨ valuation q 1242 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1220 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1248 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1220)) (literal (valuationOf q) (1240)) (literal (valuationOf q) (1248)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 1 2 (meaning1220 q) (meaning1240 q) (meaning1248 q) hs
  change valuationOf q 1220 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1220 = false ∨ valuation q 1240 = false ∨ valuation q 1248 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1221 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1248 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1221)) (literal (valuationOf q) (1239)) (literal (valuationOf q) (1248)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 2 1 (meaning1221 q) (meaning1239 q) (meaning1248 q) hs
  change valuationOf q 1221 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1221 = false ∨ valuation q 1239 = false ∨ valuation q 1248 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1221 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1249 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1221)) (literal (valuationOf q) (1240)) (literal (valuationOf q) (1249)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 2 2 (meaning1221 q) (meaning1240 q) (meaning1249 q) hs
  change valuationOf q 1221 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1221 = false ∨ valuation q 1240 = false ∨ valuation q 1249 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 1221 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1250 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1221)) (literal (valuationOf q) (1241)) (literal (valuationOf q) (1250)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 2 3 (meaning1221 q) (meaning1241 q) (meaning1250 q) hs
  change valuationOf q 1221 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 1221 = false ∨ valuation q 1241 = false ∨ valuation q 1250 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 1221 = false ∨ valuationOf q 1242 = false ∨ valuationOf q 1251 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1221)) (literal (valuationOf q) (1242)) (literal (valuationOf q) (1251)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 2 4 (meaning1221 q) (meaning1242 q) (meaning1251 q) hs
  change valuationOf q 1221 = false ∨ valuationOf q 1242 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 1221 = false ∨ valuation q 1242 = false ∨ valuation q 1251 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 1222 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1249 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1222)) (literal (valuationOf q) (1239)) (literal (valuationOf q) (1249)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 3 1 (meaning1222 q) (meaning1239 q) (meaning1249 q) hs
  change valuationOf q 1222 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 1222 = false ∨ valuation q 1239 = false ∨ valuation q 1249 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 1222 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1250 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1222)) (literal (valuationOf q) (1240)) (literal (valuationOf q) (1250)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 3 2 (meaning1222 q) (meaning1240 q) (meaning1250 q) hs
  change valuationOf q 1222 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 1222 = false ∨ valuation q 1240 = false ∨ valuation q 1250 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 1222 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1251 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1222)) (literal (valuationOf q) (1241)) (literal (valuationOf q) (1251)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 3 3 (meaning1222 q) (meaning1241 q) (meaning1251 q) hs
  change valuationOf q 1222 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 1222 = false ∨ valuation q 1241 = false ∨ valuation q 1251 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 1223 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1250 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1223)) (literal (valuationOf q) (1239)) (literal (valuationOf q) (1250)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 4 1 (meaning1223 q) (meaning1239 q) (meaning1250 q) hs
  change valuationOf q 1223 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 1223 = false ∨ valuation q 1239 = false ∨ valuation q 1250 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 1223 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1251 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1223)) (literal (valuationOf q) (1240)) (literal (valuationOf q) (1251)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 4 2 (meaning1223 q) (meaning1240 q) (meaning1251 q) hs
  change valuationOf q 1223 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 1223 = false ∨ valuation q 1240 = false ∨ valuation q 1251 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 1223 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1252 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1223)) (literal (valuationOf q) (1241)) (literal (valuationOf q) (1252)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 4 3 (meaning1223 q) (meaning1241 q) (meaning1252 q) hs
  change valuationOf q 1223 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 1223 = false ∨ valuation q 1241 = false ∨ valuation q 1252 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 1224 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1251 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1224)) (literal (valuationOf q) (1239)) (literal (valuationOf q) (1251)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 5 1 (meaning1224 q) (meaning1239 q) (meaning1251 q) hs
  change valuationOf q 1224 = false ∨ valuationOf q 1239 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 1224 = false ∨ valuation q 1239 = false ∨ valuation q 1251 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 1224 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1252 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1224)) (literal (valuationOf q) (1240)) (literal (valuationOf q) (1252)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 5 2 (meaning1224 q) (meaning1240 q) (meaning1252 q) hs
  change valuationOf q 1224 = false ∨ valuationOf q 1240 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 1224 = false ∨ valuation q 1240 = false ∨ valuation q 1252 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 1224 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1253 = true := by
  have hs : count1246 q = (countLit q [-1, -2, -5, -7, -8, -9]) + (countLit q [-11, -13, -15, -19, -20, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9]) (l₂ := [-11, -13, -15, -19, -20, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1224)) (literal (valuationOf q) (1241)) (literal (valuationOf q) (1253)) (countLit q [-1, -2, -5, -7, -8, -9]) (countLit q [-11, -13, -15, -19, -20, -23, -24]) (count1246 q) 5 3 (meaning1224 q) (meaning1241 q) (meaning1253 q) hs
  change valuationOf q 1224 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 1224 = false ∨ valuation q 1241 = false ∨ valuation q 1253 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (1259)) (countLit q [-29]) (countLit q [-30]) (count1259 q) 1 (meaningNeg30 q) (meaning1259 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1259 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1259)) (countLit q [-29]) (countLit q [-30]) (count1259 q) 1 (meaningNeg29 q) (meaning1259 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1259 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 30 = true ∨ valuationOf q 1260 = true := by
  have hs : count1259 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (1260)) (countLit q [-29]) (countLit q [-30]) (count1259 q) 1 1 (meaningNeg29 q) (meaningNeg30 q) (meaning1260 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 1260 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 1259 = false ∨ valuationOf q 1261 = true := by
  have hs : count1261 q = (countLit q [-26]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (1259)) (literal (valuationOf q) (1261)) (countLit q [-26]) (countLit q [-29, -30]) (count1261 q) 1 (meaning1259 q) (meaning1261 q) hs
  change valuationOf q 1259 = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 1259 = false ∨ valuation q 1261 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 1260 = false ∨ valuationOf q 1262 = true := by
  have hs : count1261 q = (countLit q [-26]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (1260)) (literal (valuationOf q) (1262)) (countLit q [-26]) (countLit q [-29, -30]) (count1261 q) 2 (meaning1260 q) (meaning1262 q) hs
  change valuationOf q 1260 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 1260 = false ∨ valuation q 1262 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1261 = true := by
  have hs : count1261 q = (countLit q [-26]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29, -30])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1261)) (countLit q [-26]) (countLit q [-29, -30]) (count1261 q) 1 (meaningNeg26 q) (meaning1261 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1261 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E174.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112174
