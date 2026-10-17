import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1259 = false ∨ valuationOf q 1262 = true := by
  have hs : count1261 q = (countLit q [-26]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29, -30])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (1259)) (literal (valuationOf q) (1262)) (countLit q [-26]) (countLit q [-29, -30]) (count1261 q) 1 1 (meaningNeg26 q) (meaning1259 q) (meaning1262 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1259 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1259 = false ∨ valuation q 1262 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1260 = false ∨ valuationOf q 1263 = true := by
  have hs : count1261 q = (countLit q [-26]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29, -30])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (1260)) (literal (valuationOf q) (1263)) (countLit q [-26]) (countLit q [-29, -30]) (count1261 q) 1 2 (meaningNeg26 q) (meaning1260 q) (meaning1263 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1260 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1260 = false ∨ valuation q 1263 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1264 = true := by
  have hs : count1264 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1264)) (countLit q [-35]) (countLit q [-37]) (count1264 q) 1 (meaningNeg37 q) (meaning1264 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1264 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1264 = true := by
  have hs : count1264 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1264)) (countLit q [-35]) (countLit q [-37]) (count1264 q) 1 (meaningNeg35 q) (meaning1264 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1264 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1265 = true := by
  have hs : count1264 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1265)) (countLit q [-35]) (countLit q [-37]) (count1264 q) 1 1 (meaningNeg35 q) (meaningNeg37 q) (meaning1265 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1265 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 37 = true ∨ valuation q 1265 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1266 = true := by
  have hs : count1266 q = (countLit q [-32]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -37])
  have hm := merge_right (literal (valuationOf q) (1264)) (literal (valuationOf q) (1266)) (countLit q [-32]) (countLit q [-35, -37]) (count1266 q) 1 (meaning1264 q) (meaning1266 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1266 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 1265 = false ∨ valuationOf q 1267 = true := by
  have hs : count1266 q = (countLit q [-32]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -37])
  have hm := merge_right (literal (valuationOf q) (1265)) (literal (valuationOf q) (1267)) (countLit q [-32]) (countLit q [-35, -37]) (count1266 q) 2 (meaning1265 q) (meaning1267 q) hs
  change valuationOf q 1265 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 1265 = false ∨ valuation q 1267 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1266 = true := by
  have hs : count1266 q = (countLit q [-32]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -37])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1266)) (countLit q [-32]) (countLit q [-35, -37]) (count1266 q) 1 (meaningNeg32 q) (meaning1266 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1266 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1264 = false ∨ valuationOf q 1267 = true := by
  have hs : count1266 q = (countLit q [-32]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -37])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1264)) (literal (valuationOf q) (1267)) (countLit q [-32]) (countLit q [-35, -37]) (count1266 q) 1 1 (meaningNeg32 q) (meaning1264 q) (meaning1267 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1264 = false ∨ valuation q 1267 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 1266 = false ∨ valuationOf q 1269 = true := by
  have hs : count1269 q = (countLit q [-26, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_right (literal (valuationOf q) (1266)) (literal (valuationOf q) (1269)) (countLit q [-26, -29, -30]) (countLit q [-32, -35, -37]) (count1269 q) 1 (meaning1266 q) (meaning1269 q) hs
  change valuationOf q 1266 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 1266 = false ∨ valuation q 1269 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 1261 = false ∨ valuationOf q 1269 = true := by
  have hs : count1269 q = (countLit q [-26, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_left (literal (valuationOf q) (1261)) (literal (valuationOf q) (1269)) (countLit q [-26, -29, -30]) (countLit q [-32, -35, -37]) (count1269 q) 1 (meaning1261 q) (meaning1269 q) hs
  change valuationOf q 1261 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 1261 = false ∨ valuation q 1269 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 1261 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1270 = true := by
  have hs : count1269 q = (countLit q [-26, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1261)) (literal (valuationOf q) (1266)) (literal (valuationOf q) (1270)) (countLit q [-26, -29, -30]) (countLit q [-32, -35, -37]) (count1269 q) 1 1 (meaning1261 q) (meaning1266 q) (meaning1270 q) hs
  change valuationOf q 1261 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 1261 = false ∨ valuation q 1266 = false ∨ valuation q 1270 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 1261 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1271 = true := by
  have hs : count1269 q = (countLit q [-26, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1261)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1271)) (countLit q [-26, -29, -30]) (countLit q [-32, -35, -37]) (count1269 q) 1 2 (meaning1261 q) (meaning1267 q) (meaning1271 q) hs
  change valuationOf q 1261 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 1261 = false ∨ valuation q 1267 = false ∨ valuation q 1271 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1270 = true := by
  have hs : count1269 q = (countLit q [-26, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_left (literal (valuationOf q) (1262)) (literal (valuationOf q) (1270)) (countLit q [-26, -29, -30]) (countLit q [-32, -35, -37]) (count1269 q) 2 (meaning1262 q) (meaning1270 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1270 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1271 = true := by
  have hs : count1269 q = (countLit q [-26, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1262)) (literal (valuationOf q) (1266)) (literal (valuationOf q) (1271)) (countLit q [-26, -29, -30]) (countLit q [-32, -35, -37]) (count1269 q) 2 1 (meaning1262 q) (meaning1266 q) (meaning1271 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1266 = false ∨ valuation q 1271 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1272 = true := by
  have hs : count1269 q = (countLit q [-26, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1262)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1272)) (countLit q [-26, -29, -30]) (countLit q [-32, -35, -37]) (count1269 q) 2 2 (meaning1262 q) (meaning1267 q) (meaning1272 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1267 = false ∨ valuation q 1272 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1271 = true := by
  have hs : count1269 q = (countLit q [-26, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_left (literal (valuationOf q) (1263)) (literal (valuationOf q) (1271)) (countLit q [-26, -29, -30]) (countLit q [-32, -35, -37]) (count1269 q) 3 (meaning1263 q) (meaning1271 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1271 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1272 = true := by
  have hs : count1269 q = (countLit q [-26, -29, -30]) + (countLit q [-32, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30]) (l₂ := [-32, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1266)) (literal (valuationOf q) (1272)) (countLit q [-26, -29, -30]) (countLit q [-32, -35, -37]) (count1269 q) 3 1 (meaning1263 q) (meaning1266 q) (meaning1272 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1266 = false ∨ valuation q 1272 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1275 = true := by
  have hs : count1275 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1275)) (countLit q [-40]) (countLit q [-42]) (count1275 q) 1 (meaningNeg40 q) (meaning1275 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1275 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1276 = true := by
  have hs : count1275 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1276)) (countLit q [-40]) (countLit q [-42]) (count1275 q) 1 1 (meaningNeg40 q) (meaningNeg42 q) (meaning1276 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1276 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 1276 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-39]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1275)) (literal (valuationOf q) (1277)) (countLit q [-39]) (countLit q [-40, -42]) (count1277 q) 1 (meaning1275 q) (meaning1277 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1277 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 1276 = false ∨ valuationOf q 1278 = true := by
  have hs : count1277 q = (countLit q [-39]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1276)) (literal (valuationOf q) (1278)) (countLit q [-39]) (countLit q [-40, -42]) (count1277 q) 2 (meaning1276 q) (meaning1278 q) hs
  change valuationOf q 1276 = false ∨ valuationOf q 1278 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 1276 = false ∨ valuation q 1278 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-39]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -42])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1277)) (countLit q [-39]) (countLit q [-40, -42]) (count1277 q) 1 (meaningNeg39 q) (meaning1277 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1277 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1275 = false ∨ valuationOf q 1278 = true := by
  have hs : count1277 q = (countLit q [-39]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (1275)) (literal (valuationOf q) (1278)) (countLit q [-39]) (countLit q [-40, -42]) (count1277 q) 1 1 (meaningNeg39 q) (meaning1275 q) (meaning1278 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1275 = false ∨ valuationOf q 1278 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1275 = false ∨ valuation q 1278 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1280 = true := by
  have hs : count1280 q = (countLit q [-44]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1280)) (countLit q [-44]) (countLit q [-46]) (count1280 q) 1 (meaningNeg46 q) (meaning1280 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1280 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1280 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1280 = true := by
  have hs : count1280 q = (countLit q [-44]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1280)) (countLit q [-44]) (countLit q [-46]) (count1280 q) 1 (meaningNeg44 q) (meaning1280 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1280 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1280 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 46 = true ∨ valuationOf q 1281 = true := by
  have hs : count1280 q = (countLit q [-44]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (1281)) (countLit q [-44]) (countLit q [-46]) (count1280 q) 1 1 (meaningNeg44 q) (meaningNeg46 q) (meaning1281 q) hs
  change (! (valuationOf q 44)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 46 = true ∨ valuation q 1281 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1282 = true := by
  have hs : count1282 q = (countLit q [-47]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1282)) (countLit q [-47]) (countLit q [-49]) (count1282 q) 1 (meaningNeg49 q) (meaning1282 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1282 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1282 = true := by
  have hs : count1282 q = (countLit q [-47]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1282)) (countLit q [-47]) (countLit q [-49]) (count1282 q) 1 (meaningNeg47 q) (meaning1282 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1282 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 1282 = false ∨ valuationOf q 1284 = true := by
  have hs : count1284 q = (countLit q [-44, -46]) + (countLit q [-47, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-47, -49])
  have hm := merge_right (literal (valuationOf q) (1282)) (literal (valuationOf q) (1284)) (countLit q [-44, -46]) (countLit q [-47, -49]) (count1284 q) 1 (meaning1282 q) (meaning1284 q) hs
  change valuationOf q 1282 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 1282 = false ∨ valuation q 1284 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1284 = true := by
  have hs : count1284 q = (countLit q [-44, -46]) + (countLit q [-47, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-47, -49])
  have hm := merge_left (literal (valuationOf q) (1280)) (literal (valuationOf q) (1284)) (countLit q [-44, -46]) (countLit q [-47, -49]) (count1284 q) 1 (meaning1280 q) (meaning1284 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1284 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1285 = true := by
  have hs : count1284 q = (countLit q [-44, -46]) + (countLit q [-47, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-47, -49])
  have hm := merge_two (literal (valuationOf q) (1280)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1285)) (countLit q [-44, -46]) (countLit q [-47, -49]) (count1284 q) 1 1 (meaning1280 q) (meaning1282 q) (meaning1285 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1282 = false ∨ valuation q 1285 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E174.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112174
