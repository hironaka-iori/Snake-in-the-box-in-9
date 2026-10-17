import E112242Semantics
import B112E242Inputs
namespace Snake9.Regrowth.E112242
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause129 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1313 = true := by
  have hs : count1313 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1313)) (countLit q [-64]) (countLit q [-65]) (count1313 q) 1 (meaningNeg64 q) (meaning1313 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1313 = true := counterClause129 (baseVal q)

theorem counterClause130 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1315 = true := by
  have hs : count1315 q = (countLit q [-59, -61]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-59, -61]) (l₂ := [-64, -65])
  have hm := merge_right (literal (valuationOf q) (1313)) (literal (valuationOf q) (1315)) (countLit q [-59, -61]) (countLit q [-64, -65]) (count1315 q) 1 (meaning1313 q) (meaning1315 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1315 = true := counterClause130 (baseVal q)

theorem counterClause131 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1316 = true := by
  have hs : count1315 q = (countLit q [-59, -61]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-59, -61]) (l₂ := [-64, -65])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1316)) (countLit q [-59, -61]) (countLit q [-64, -65]) (count1315 q) 1 1 (meaning1311 q) (meaning1313 q) (meaning1316 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1313 = false ∨ valuation q 1316 = true := counterClause131 (baseVal q)

theorem counterClause132 (q : Nat → Bool) : valuationOf q 1316 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-52, -57, -58]) + (countLit q [-59, -61, -64, -65]) := List.countP_append (p := literal q) (l₁ := [-52, -57, -58]) (l₂ := [-59, -61, -64, -65])
  have hm := merge_right (literal (valuationOf q) (1316)) (literal (valuationOf q) (1320)) (countLit q [-52, -57, -58]) (countLit q [-59, -61, -64, -65]) (count1319 q) 2 (meaning1316 q) (meaning1320 q) hs
  change valuationOf q 1316 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 1316 = false ∨ valuation q 1320 = true := counterClause132 (baseVal q)

theorem counterClause133 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-52, -57, -58]) + (countLit q [-59, -61, -64, -65]) := List.countP_append (p := literal q) (l₁ := [-52, -57, -58]) (l₂ := [-59, -61, -64, -65])
  have hm := merge_left (literal (valuationOf q) (1308)) (literal (valuationOf q) (1319)) (countLit q [-52, -57, -58]) (countLit q [-59, -61, -64, -65]) (count1319 q) 1 (meaning1308 q) (meaning1319 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1319 = true := counterClause133 (baseVal q)

theorem counterClause134 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1315 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-52, -57, -58]) + (countLit q [-59, -61, -64, -65]) := List.countP_append (p := literal q) (l₁ := [-52, -57, -58]) (l₂ := [-59, -61, -64, -65])
  have hm := merge_two (literal (valuationOf q) (1308)) (literal (valuationOf q) (1315)) (literal (valuationOf q) (1320)) (countLit q [-52, -57, -58]) (countLit q [-59, -61, -64, -65]) (count1319 q) 1 1 (meaning1308 q) (meaning1315 q) (meaning1320 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1315 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1315 = false ∨ valuation q 1320 = true := counterClause134 (baseVal q)

theorem counterClause135 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-52, -57, -58]) + (countLit q [-59, -61, -64, -65]) := List.countP_append (p := literal q) (l₁ := [-52, -57, -58]) (l₂ := [-59, -61, -64, -65])
  have hm := merge_left (literal (valuationOf q) (1309)) (literal (valuationOf q) (1320)) (countLit q [-52, -57, -58]) (countLit q [-59, -61, -64, -65]) (count1319 q) 2 (meaning1309 q) (meaning1320 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1320 = true := counterClause135 (baseVal q)

theorem counterClause136 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1315 = false ∨ valuationOf q 1321 = true := by
  have hs : count1319 q = (countLit q [-52, -57, -58]) + (countLit q [-59, -61, -64, -65]) := List.countP_append (p := literal q) (l₁ := [-52, -57, -58]) (l₂ := [-59, -61, -64, -65])
  have hm := merge_two (literal (valuationOf q) (1309)) (literal (valuationOf q) (1315)) (literal (valuationOf q) (1321)) (countLit q [-52, -57, -58]) (countLit q [-59, -61, -64, -65]) (count1319 q) 2 1 (meaning1309 q) (meaning1315 q) (meaning1321 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1315 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1315 = false ∨ valuation q 1321 = true := counterClause136 (baseVal q)

theorem counterClause137 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1326)) (countLit q [-67]) (countLit q [-70]) (count1326 q) 1 (meaningNeg70 q) (meaning1326 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1326 = true := counterClause137 (baseVal q)

theorem counterClause138 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1328 = true := by
  have hs : count1328 q = (countLit q [-66]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67, -70])
  have hm := merge_right (literal (valuationOf q) (1326)) (literal (valuationOf q) (1328)) (countLit q [-66]) (countLit q [-67, -70]) (count1328 q) 1 (meaning1326 q) (meaning1328 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1328 = true := counterClause138 (baseVal q)

theorem counterClause139 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1331 = true := by
  have hs : count1331 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1331)) (countLit q [-72]) (countLit q [-73]) (count1331 q) 1 (meaningNeg73 q) (meaning1331 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1331 = true := counterClause139 (baseVal q)

theorem counterClause140 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1332 = true := by
  have hs : count1331 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1332)) (countLit q [-72]) (countLit q [-73]) (count1331 q) 1 1 (meaningNeg72 q) (meaningNeg73 q) (meaning1332 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 73 = true ∨ valuation q 1332 = true := counterClause140 (baseVal q)

theorem counterClause141 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1333 = true := by
  have hs : count1333 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1333)) (countLit q [-75]) (countLit q [-77]) (count1333 q) 1 (meaningNeg77 q) (meaning1333 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1333 = true := counterClause141 (baseVal q)

theorem counterClause142 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1336 = true := by
  have hs : count1335 q = (countLit q [-72, -73]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-75, -77])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1333)) (literal (valuationOf q) (1336)) (countLit q [-72, -73]) (countLit q [-75, -77]) (count1335 q) 1 1 (meaning1331 q) (meaning1333 q) (meaning1336 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1333 = false ∨ valuation q 1336 = true := counterClause142 (baseVal q)

theorem counterClause143 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1337 = true := by
  have hs : count1335 q = (countLit q [-72, -73]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-75, -77])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1333)) (literal (valuationOf q) (1337)) (countLit q [-72, -73]) (countLit q [-75, -77]) (count1335 q) 2 1 (meaning1332 q) (meaning1333 q) (meaning1337 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1333 = false ∨ valuation q 1337 = true := counterClause143 (baseVal q)

theorem counterClause144 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1340 = true := by
  have hs : count1339 q = (countLit q [-66, -67, -70]) + (countLit q [-72, -73, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-66, -67, -70]) (l₂ := [-72, -73, -75, -77])
  have hm := merge_right (literal (valuationOf q) (1336)) (literal (valuationOf q) (1340)) (countLit q [-66, -67, -70]) (countLit q [-72, -73, -75, -77]) (count1339 q) 2 (meaning1336 q) (meaning1340 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1340 = true := counterClause144 (baseVal q)

theorem counterClause145 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1341 = true := by
  have hs : count1339 q = (countLit q [-66, -67, -70]) + (countLit q [-72, -73, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-66, -67, -70]) (l₂ := [-72, -73, -75, -77])
  have hm := merge_right (literal (valuationOf q) (1337)) (literal (valuationOf q) (1341)) (countLit q [-66, -67, -70]) (countLit q [-72, -73, -75, -77]) (count1339 q) 3 (meaning1337 q) (meaning1341 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1341 = true := counterClause145 (baseVal q)

theorem counterClause146 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1336 = false ∨ valuationOf q 1341 = true := by
  have hs : count1339 q = (countLit q [-66, -67, -70]) + (countLit q [-72, -73, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-66, -67, -70]) (l₂ := [-72, -73, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1336)) (literal (valuationOf q) (1341)) (countLit q [-66, -67, -70]) (countLit q [-72, -73, -75, -77]) (count1339 q) 1 2 (meaning1328 q) (meaning1336 q) (meaning1341 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1336 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1336 = false ∨ valuation q 1341 = true := counterClause146 (baseVal q)

theorem counterClause147 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1349 = true := by
  have hs : count1346 q = (countLit q [-52, -57, -58, -59, -61, -64, -65]) + (countLit q [-66, -67, -70, -72, -73, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-52, -57, -58, -59, -61, -64, -65]) (l₂ := [-66, -67, -70, -72, -73, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1341)) (literal (valuationOf q) (1349)) (countLit q [-52, -57, -58, -59, -61, -64, -65]) (countLit q [-66, -67, -70, -72, -73, -75, -77]) (count1346 q) 1 3 (meaning1319 q) (meaning1341 q) (meaning1349 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1341 = false ∨ valuation q 1349 = true := counterClause147 (baseVal q)

theorem counterClause148 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1349 = true := by
  have hs : count1346 q = (countLit q [-52, -57, -58, -59, -61, -64, -65]) + (countLit q [-66, -67, -70, -72, -73, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-52, -57, -58, -59, -61, -64, -65]) (l₂ := [-66, -67, -70, -72, -73, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1320)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1349)) (countLit q [-52, -57, -58, -59, -61, -64, -65]) (countLit q [-66, -67, -70, -72, -73, -75, -77]) (count1346 q) 2 2 (meaning1320 q) (meaning1340 q) (meaning1349 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1340 = false ∨ valuation q 1349 = true := counterClause148 (baseVal q)

theorem counterClause149 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1350 = true := by
  have hs : count1346 q = (countLit q [-52, -57, -58, -59, -61, -64, -65]) + (countLit q [-66, -67, -70, -72, -73, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-52, -57, -58, -59, -61, -64, -65]) (l₂ := [-66, -67, -70, -72, -73, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1320)) (literal (valuationOf q) (1341)) (literal (valuationOf q) (1350)) (countLit q [-52, -57, -58, -59, -61, -64, -65]) (countLit q [-66, -67, -70, -72, -73, -75, -77]) (count1346 q) 2 3 (meaning1320 q) (meaning1341 q) (meaning1350 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1341 = false ∨ valuation q 1350 = true := counterClause149 (baseVal q)

theorem counterClause150 (q : Nat → Bool) : valuationOf q 1321 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1350 = true := by
  have hs : count1346 q = (countLit q [-52, -57, -58, -59, -61, -64, -65]) + (countLit q [-66, -67, -70, -72, -73, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-52, -57, -58, -59, -61, -64, -65]) (l₂ := [-66, -67, -70, -72, -73, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1321)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1350)) (countLit q [-52, -57, -58, -59, -61, -64, -65]) (countLit q [-66, -67, -70, -72, -73, -75, -77]) (count1346 q) 3 2 (meaning1321 q) (meaning1340 q) (meaning1350 q) hs
  change valuationOf q 1321 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 1321 = false ∨ valuation q 1340 = false ∨ valuation q 1350 = true := counterClause150 (baseVal q)

theorem counterClause151 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-78]) + (countLit q [-82, -83]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-82, -83])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1362)) (countLit q [-78]) (countLit q [-82, -83]) (count1362 q) 1 (meaningNeg78 q) (meaning1362 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1362 = true := counterClause151 (baseVal q)

theorem counterClause152 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (1365)) (countLit q [-85]) (countLit q [-87]) (count1365 q) 1 (meaningNeg87 q) (meaning1365 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1365 = true := counterClause152 (baseVal q)

theorem counterClause153 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1367 = true := by
  have hs : count1367 q = (countLit q [-88]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (1367)) (countLit q [-88]) (countLit q [-91]) (count1367 q) 1 (meaningNeg91 q) (meaning1367 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1367 = true := counterClause153 (baseVal q)

theorem counterClause154 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1369 = true := by
  have hs : count1369 q = (countLit q [-85, -87]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-88, -91])
  have hm := merge_left (literal (valuationOf q) (1365)) (literal (valuationOf q) (1369)) (countLit q [-85, -87]) (countLit q [-88, -91]) (count1369 q) 1 (meaning1365 q) (meaning1369 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1369 = true := counterClause154 (baseVal q)

theorem counterClause155 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1370 = true := by
  have hs : count1369 q = (countLit q [-85, -87]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-88, -91])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1370)) (countLit q [-85, -87]) (countLit q [-88, -91]) (count1369 q) 1 1 (meaning1365 q) (meaning1367 q) (meaning1370 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1367 = false ∨ valuation q 1370 = true := counterClause155 (baseVal q)

theorem counterClause156 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-78, -82, -83]) + (countLit q [-85, -87, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-78, -82, -83]) (l₂ := [-85, -87, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1369)) (literal (valuationOf q) (1374)) (countLit q [-78, -82, -83]) (countLit q [-85, -87, -88, -91]) (count1373 q) 1 1 (meaning1362 q) (meaning1369 q) (meaning1374 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1369 = false ∨ valuation q 1374 = true := counterClause156 (baseVal q)

theorem counterClause157 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-78, -82, -83]) + (countLit q [-85, -87, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-78, -82, -83]) (l₂ := [-85, -87, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1375)) (countLit q [-78, -82, -83]) (countLit q [-85, -87, -88, -91]) (count1373 q) 1 2 (meaning1362 q) (meaning1370 q) (meaning1375 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1370 = false ∨ valuation q 1375 = true := counterClause157 (baseVal q)

theorem counterClause158 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1380 = true := by
  have hs : count1380 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1380)) (countLit q [-93]) (countLit q [-94]) (count1380 q) 1 (meaningNeg94 q) (meaning1380 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1380 = true := counterClause158 (baseVal q)

theorem counterClause159 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1380 = true := by
  have hs : count1380 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1380)) (countLit q [-93]) (countLit q [-94]) (count1380 q) 1 (meaningNeg93 q) (meaning1380 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1380 = true := counterClause159 (baseVal q)

theorem counterClause160 (q : Nat → Bool) : valuationOf q 1380 = false ∨ valuationOf q 1382 = true := by
  have hs : count1382 q = (countLit q [-92]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -94])
  have hm := merge_right (literal (valuationOf q) (1380)) (literal (valuationOf q) (1382)) (countLit q [-92]) (countLit q [-93, -94]) (count1382 q) 1 (meaning1380 q) (meaning1382 q) hs
  change valuationOf q 1380 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 1380 = false ∨ valuation q 1382 = true := counterClause160 (baseVal q)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E242.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112242
