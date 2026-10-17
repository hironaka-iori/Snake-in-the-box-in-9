import E112098Semantics
import B112E098Inputs
namespace Snake9.Regrowth.E112098
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause97 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1212 = true := by
  have hs : count1212 q = (countLit q [-26]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1212)) (countLit q [-26]) (countLit q [-29]) (count1212 q) 1 (meaningNeg26 q) (meaning1212 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1212 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1212 = true := counterClause97 (baseVal q)

theorem counterClause98 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 29 = true ∨ valuationOf q 1213 = true := by
  have hs : count1212 q = (countLit q [-26]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (-29)) (literal (valuationOf q) (1213)) (countLit q [-26]) (countLit q [-29]) (count1212 q) 1 1 (meaningNeg26 q) (meaningNeg29 q) (meaning1213 q) hs
  change (! (valuationOf q 26)) = false ∨ (! (valuationOf q 29)) = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 29 = true ∨ valuation q 1213 = true := counterClause98 (baseVal q)

theorem counterClause99 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1214 = true := by
  have hs : count1214 q = (countLit q [-24]) + (countLit q [-26, -29]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26, -29])
  have hm := merge_right (literal (valuationOf q) (1212)) (literal (valuationOf q) (1214)) (countLit q [-24]) (countLit q [-26, -29]) (count1214 q) 1 (meaning1212 q) (meaning1214 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1214 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1214 = true := counterClause99 (baseVal q)

theorem counterClause100 (q : Nat → Bool) : valuationOf q 1213 = false ∨ valuationOf q 1215 = true := by
  have hs : count1214 q = (countLit q [-24]) + (countLit q [-26, -29]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26, -29])
  have hm := merge_right (literal (valuationOf q) (1213)) (literal (valuationOf q) (1215)) (countLit q [-24]) (countLit q [-26, -29]) (count1214 q) 2 (meaning1213 q) (meaning1215 q) hs
  change valuationOf q 1213 = false ∨ valuationOf q 1215 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 1213 = false ∨ valuation q 1215 = true := counterClause100 (baseVal q)

theorem counterClause101 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1214 = true := by
  have hs : count1214 q = (countLit q [-24]) + (countLit q [-26, -29]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26, -29])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1214)) (countLit q [-24]) (countLit q [-26, -29]) (count1214 q) 1 (meaningNeg24 q) (meaning1214 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1214 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1214 = true := counterClause101 (baseVal q)

theorem counterClause102 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1212 = false ∨ valuationOf q 1215 = true := by
  have hs : count1214 q = (countLit q [-24]) + (countLit q [-26, -29]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26, -29])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (1212)) (literal (valuationOf q) (1215)) (countLit q [-24]) (countLit q [-26, -29]) (count1214 q) 1 1 (meaningNeg24 q) (meaning1212 q) (meaning1215 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1212 = false ∨ valuationOf q 1215 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1212 = false ∨ valuation q 1215 = true := counterClause102 (baseVal q)

theorem counterClause103 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1217 = true := by
  have hs : count1217 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1217)) (countLit q [-34]) (countLit q [-35]) (count1217 q) 1 (meaningNeg35 q) (meaning1217 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1217 = true := counterClause103 (baseVal q)

theorem counterClause104 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1217 = true := by
  have hs : count1217 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1217)) (countLit q [-34]) (countLit q [-35]) (count1217 q) 1 (meaningNeg34 q) (meaning1217 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1217 = true := counterClause104 (baseVal q)

theorem counterClause105 (q : Nat → Bool) : valuationOf q 1217 = false ∨ valuationOf q 1219 = true := by
  have hs : count1219 q = (countLit q [-30]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1217)) (literal (valuationOf q) (1219)) (countLit q [-30]) (countLit q [-34, -35]) (count1219 q) 1 (meaning1217 q) (meaning1219 q) hs
  change valuationOf q 1217 = false ∨ valuationOf q 1219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 1217 = false ∨ valuation q 1219 = true := counterClause105 (baseVal q)

theorem counterClause106 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1219 = true := by
  have hs : count1219 q = (countLit q [-30]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-34, -35])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1219)) (countLit q [-30]) (countLit q [-34, -35]) (count1219 q) 1 (meaningNeg30 q) (meaning1219 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1219 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1219 = true := counterClause106 (baseVal q)

theorem counterClause107 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1217 = false ∨ valuationOf q 1220 = true := by
  have hs : count1219 q = (countLit q [-30]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-34, -35])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1220)) (countLit q [-30]) (countLit q [-34, -35]) (count1219 q) 1 1 (meaningNeg30 q) (meaning1217 q) (meaning1220 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1220 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1217 = false ∨ valuation q 1220 = true := counterClause107 (baseVal q)

theorem counterClause108 (q : Nat → Bool) : valuationOf q 1219 = false ∨ valuationOf q 1222 = true := by
  have hs : count1222 q = (countLit q [-24, -26, -29]) + (countLit q [-30, -34, -35]) := List.countP_append (p := literal q) (l₁ := [-24, -26, -29]) (l₂ := [-30, -34, -35])
  have hm := merge_right (literal (valuationOf q) (1219)) (literal (valuationOf q) (1222)) (countLit q [-24, -26, -29]) (countLit q [-30, -34, -35]) (count1222 q) 1 (meaning1219 q) (meaning1222 q) hs
  change valuationOf q 1219 = false ∨ valuationOf q 1222 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 1219 = false ∨ valuation q 1222 = true := counterClause108 (baseVal q)

theorem counterClause109 (q : Nat → Bool) : valuationOf q 1220 = false ∨ valuationOf q 1223 = true := by
  have hs : count1222 q = (countLit q [-24, -26, -29]) + (countLit q [-30, -34, -35]) := List.countP_append (p := literal q) (l₁ := [-24, -26, -29]) (l₂ := [-30, -34, -35])
  have hm := merge_right (literal (valuationOf q) (1220)) (literal (valuationOf q) (1223)) (countLit q [-24, -26, -29]) (countLit q [-30, -34, -35]) (count1222 q) 2 (meaning1220 q) (meaning1223 q) hs
  change valuationOf q 1220 = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 1220 = false ∨ valuation q 1223 = true := counterClause109 (baseVal q)

theorem counterClause110 (q : Nat → Bool) : valuationOf q 1214 = false ∨ valuationOf q 1222 = true := by
  have hs : count1222 q = (countLit q [-24, -26, -29]) + (countLit q [-30, -34, -35]) := List.countP_append (p := literal q) (l₁ := [-24, -26, -29]) (l₂ := [-30, -34, -35])
  have hm := merge_left (literal (valuationOf q) (1214)) (literal (valuationOf q) (1222)) (countLit q [-24, -26, -29]) (countLit q [-30, -34, -35]) (count1222 q) 1 (meaning1214 q) (meaning1222 q) hs
  change valuationOf q 1214 = false ∨ valuationOf q 1222 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 1214 = false ∨ valuation q 1222 = true := counterClause110 (baseVal q)

theorem counterClause111 (q : Nat → Bool) : valuationOf q 1214 = false ∨ valuationOf q 1219 = false ∨ valuationOf q 1223 = true := by
  have hs : count1222 q = (countLit q [-24, -26, -29]) + (countLit q [-30, -34, -35]) := List.countP_append (p := literal q) (l₁ := [-24, -26, -29]) (l₂ := [-30, -34, -35])
  have hm := merge_two (literal (valuationOf q) (1214)) (literal (valuationOf q) (1219)) (literal (valuationOf q) (1223)) (countLit q [-24, -26, -29]) (countLit q [-30, -34, -35]) (count1222 q) 1 1 (meaning1214 q) (meaning1219 q) (meaning1223 q) hs
  change valuationOf q 1214 = false ∨ valuationOf q 1219 = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 1214 = false ∨ valuation q 1219 = false ∨ valuation q 1223 = true := counterClause111 (baseVal q)

theorem counterClause112 (q : Nat → Bool) : valuationOf q 1215 = false ∨ valuationOf q 1219 = false ∨ valuationOf q 1224 = true := by
  have hs : count1222 q = (countLit q [-24, -26, -29]) + (countLit q [-30, -34, -35]) := List.countP_append (p := literal q) (l₁ := [-24, -26, -29]) (l₂ := [-30, -34, -35])
  have hm := merge_two (literal (valuationOf q) (1215)) (literal (valuationOf q) (1219)) (literal (valuationOf q) (1224)) (countLit q [-24, -26, -29]) (countLit q [-30, -34, -35]) (count1222 q) 2 1 (meaning1215 q) (meaning1219 q) (meaning1224 q) hs
  change valuationOf q 1215 = false ∨ valuationOf q 1219 = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 1215 = false ∨ valuation q 1219 = false ∨ valuation q 1224 = true := counterClause112 (baseVal q)

theorem counterClause113 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1228 = true := by
  have hs : count1228 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1228)) (countLit q [-38]) (countLit q [-40]) (count1228 q) 1 (meaningNeg40 q) (meaning1228 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1228 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1228 = true := counterClause113 (baseVal q)

theorem counterClause114 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1228 = true := by
  have hs : count1228 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1228)) (countLit q [-38]) (countLit q [-40]) (count1228 q) 1 (meaningNeg38 q) (meaning1228 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1228 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1228 = true := counterClause114 (baseVal q)

theorem counterClause115 (q : Nat → Bool) : valuationOf q 1228 = false ∨ valuationOf q 1230 = true := by
  have hs : count1230 q = (countLit q [-37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1228)) (literal (valuationOf q) (1230)) (countLit q [-37]) (countLit q [-38, -40]) (count1230 q) 1 (meaning1228 q) (meaning1230 q) hs
  change valuationOf q 1228 = false ∨ valuationOf q 1230 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 1228 = false ∨ valuation q 1230 = true := counterClause115 (baseVal q)

theorem counterClause116 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1230 = true := by
  have hs : count1230 q = (countLit q [-37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38, -40])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1230)) (countLit q [-37]) (countLit q [-38, -40]) (count1230 q) 1 (meaningNeg37 q) (meaning1230 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1230 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1230 = true := counterClause116 (baseVal q)

theorem counterClause117 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1233 = true := by
  have hs : count1233 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1233)) (countLit q [-42]) (countLit q [-45]) (count1233 q) 1 (meaningNeg45 q) (meaning1233 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1233 = true := counterClause117 (baseVal q)

theorem counterClause118 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1233 = true := by
  have hs : count1233 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1233)) (countLit q [-42]) (countLit q [-45]) (count1233 q) 1 (meaningNeg42 q) (meaning1233 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1233 = true := counterClause118 (baseVal q)

theorem counterClause119 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1235 = true := by
  have hs : count1235 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1235)) (countLit q [-46]) (countLit q [-48]) (count1235 q) 1 (meaningNeg46 q) (meaning1235 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1235 = true := counterClause119 (baseVal q)

theorem counterClause120 (q : Nat → Bool) : valuationOf q 1235 = false ∨ valuationOf q 1237 = true := by
  have hs : count1237 q = (countLit q [-42, -45]) + (countLit q [-46, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-46, -48])
  have hm := merge_right (literal (valuationOf q) (1235)) (literal (valuationOf q) (1237)) (countLit q [-42, -45]) (countLit q [-46, -48]) (count1237 q) 1 (meaning1235 q) (meaning1237 q) hs
  change valuationOf q 1235 = false ∨ valuationOf q 1237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 1235 = false ∨ valuation q 1237 = true := counterClause120 (baseVal q)

theorem counterClause121 (q : Nat → Bool) : valuationOf q 1233 = false ∨ valuationOf q 1237 = true := by
  have hs : count1237 q = (countLit q [-42, -45]) + (countLit q [-46, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-46, -48])
  have hm := merge_left (literal (valuationOf q) (1233)) (literal (valuationOf q) (1237)) (countLit q [-42, -45]) (countLit q [-46, -48]) (count1237 q) 1 (meaning1233 q) (meaning1237 q) hs
  change valuationOf q 1233 = false ∨ valuationOf q 1237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 1233 = false ∨ valuation q 1237 = true := counterClause121 (baseVal q)

theorem counterClause122 (q : Nat → Bool) : valuationOf q 1233 = false ∨ valuationOf q 1235 = false ∨ valuationOf q 1238 = true := by
  have hs : count1237 q = (countLit q [-42, -45]) + (countLit q [-46, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-46, -48])
  have hm := merge_two (literal (valuationOf q) (1233)) (literal (valuationOf q) (1235)) (literal (valuationOf q) (1238)) (countLit q [-42, -45]) (countLit q [-46, -48]) (count1237 q) 1 1 (meaning1233 q) (meaning1235 q) (meaning1238 q) hs
  change valuationOf q 1233 = false ∨ valuationOf q 1235 = false ∨ valuationOf q 1238 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 1233 = false ∨ valuation q 1235 = false ∨ valuation q 1238 = true := counterClause122 (baseVal q)

theorem counterClause123 (q : Nat → Bool) : valuationOf q 1237 = false ∨ valuationOf q 1241 = true := by
  have hs : count1241 q = (countLit q [-37, -38, -40]) + (countLit q [-42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-37, -38, -40]) (l₂ := [-42, -45, -46, -48])
  have hm := merge_right (literal (valuationOf q) (1237)) (literal (valuationOf q) (1241)) (countLit q [-37, -38, -40]) (countLit q [-42, -45, -46, -48]) (count1241 q) 1 (meaning1237 q) (meaning1241 q) hs
  change valuationOf q 1237 = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 1237 = false ∨ valuation q 1241 = true := counterClause123 (baseVal q)

theorem counterClause124 (q : Nat → Bool) : valuationOf q 1238 = false ∨ valuationOf q 1242 = true := by
  have hs : count1241 q = (countLit q [-37, -38, -40]) + (countLit q [-42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-37, -38, -40]) (l₂ := [-42, -45, -46, -48])
  have hm := merge_right (literal (valuationOf q) (1238)) (literal (valuationOf q) (1242)) (countLit q [-37, -38, -40]) (countLit q [-42, -45, -46, -48]) (count1241 q) 2 (meaning1238 q) (meaning1242 q) hs
  change valuationOf q 1238 = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 1238 = false ∨ valuation q 1242 = true := counterClause124 (baseVal q)

theorem counterClause125 (q : Nat → Bool) : valuationOf q 1230 = false ∨ valuationOf q 1241 = true := by
  have hs : count1241 q = (countLit q [-37, -38, -40]) + (countLit q [-42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-37, -38, -40]) (l₂ := [-42, -45, -46, -48])
  have hm := merge_left (literal (valuationOf q) (1230)) (literal (valuationOf q) (1241)) (countLit q [-37, -38, -40]) (countLit q [-42, -45, -46, -48]) (count1241 q) 1 (meaning1230 q) (meaning1241 q) hs
  change valuationOf q 1230 = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 1230 = false ∨ valuation q 1241 = true := counterClause125 (baseVal q)

theorem counterClause126 (q : Nat → Bool) : valuationOf q 1230 = false ∨ valuationOf q 1237 = false ∨ valuationOf q 1242 = true := by
  have hs : count1241 q = (countLit q [-37, -38, -40]) + (countLit q [-42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-37, -38, -40]) (l₂ := [-42, -45, -46, -48])
  have hm := merge_two (literal (valuationOf q) (1230)) (literal (valuationOf q) (1237)) (literal (valuationOf q) (1242)) (countLit q [-37, -38, -40]) (countLit q [-42, -45, -46, -48]) (count1241 q) 1 1 (meaning1230 q) (meaning1237 q) (meaning1242 q) hs
  change valuationOf q 1230 = false ∨ valuationOf q 1237 = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 1230 = false ∨ valuation q 1237 = false ∨ valuation q 1242 = true := counterClause126 (baseVal q)

theorem counterClause127 (q : Nat → Bool) : valuationOf q 1241 = false ∨ valuationOf q 1248 = true := by
  have hs : count1248 q = (countLit q [-24, -26, -29, -30, -34, -35]) + (countLit q [-37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-24, -26, -29, -30, -34, -35]) (l₂ := [-37, -38, -40, -42, -45, -46, -48])
  have hm := merge_right (literal (valuationOf q) (1241)) (literal (valuationOf q) (1248)) (countLit q [-24, -26, -29, -30, -34, -35]) (countLit q [-37, -38, -40, -42, -45, -46, -48]) (count1248 q) 1 (meaning1241 q) (meaning1248 q) hs
  change valuationOf q 1241 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 1241 = false ∨ valuation q 1248 = true := counterClause127 (baseVal q)

theorem counterClause128 (q : Nat → Bool) : valuationOf q 1242 = false ∨ valuationOf q 1249 = true := by
  have hs : count1248 q = (countLit q [-24, -26, -29, -30, -34, -35]) + (countLit q [-37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-24, -26, -29, -30, -34, -35]) (l₂ := [-37, -38, -40, -42, -45, -46, -48])
  have hm := merge_right (literal (valuationOf q) (1242)) (literal (valuationOf q) (1249)) (countLit q [-24, -26, -29, -30, -34, -35]) (countLit q [-37, -38, -40, -42, -45, -46, -48]) (count1248 q) 2 (meaning1242 q) (meaning1249 q) hs
  change valuationOf q 1242 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 1242 = false ∨ valuation q 1249 = true := counterClause128 (baseVal q)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E098.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112098
