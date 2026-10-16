import E112184Semantics
import B112E184Inputs
namespace Snake9.Regrowth.E112184
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause97 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1311)) (countLit q [-74]) (countLit q [-76]) (count1311 q) 1 (meaningNeg74 q) (meaning1311 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1311 = true := counterClause97 (baseVal q)

theorem counterClause98 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1313 = true := by
  have hs : count1313 q = (countLit q [-72]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74, -76])
  have hm := merge_right (literal (valuationOf q) (1311)) (literal (valuationOf q) (1313)) (countLit q [-72]) (countLit q [-74, -76]) (count1313 q) 1 (meaning1311 q) (meaning1313 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1313 = true := counterClause98 (baseVal q)

theorem counterClause99 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1313 = true := by
  have hs : count1313 q = (countLit q [-72]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74, -76])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1313)) (countLit q [-72]) (countLit q [-74, -76]) (count1313 q) 1 (meaningNeg72 q) (meaning1313 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1313 = true := counterClause99 (baseVal q)

theorem counterClause100 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1311 = false ∨ valuationOf q 1314 = true := by
  have hs : count1313 q = (countLit q [-72]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74, -76])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (1311)) (literal (valuationOf q) (1314)) (countLit q [-72]) (countLit q [-74, -76]) (count1313 q) 1 1 (meaningNeg72 q) (meaning1311 q) (meaning1314 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1311 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1311 = false ∨ valuation q 1314 = true := counterClause100 (baseVal q)

theorem counterClause101 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1316 = true := by
  have hs : count1316 q = (countLit q [-66, -69, -70]) + (countLit q [-72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-66, -69, -70]) (l₂ := [-72, -74, -76])
  have hm := merge_left (literal (valuationOf q) (1308)) (literal (valuationOf q) (1316)) (countLit q [-66, -69, -70]) (countLit q [-72, -74, -76]) (count1316 q) 1 (meaning1308 q) (meaning1316 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1316 = true := counterClause101 (baseVal q)

theorem counterClause102 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1317 = true := by
  have hs : count1316 q = (countLit q [-66, -69, -70]) + (countLit q [-72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-66, -69, -70]) (l₂ := [-72, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1308)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1317)) (countLit q [-66, -69, -70]) (countLit q [-72, -74, -76]) (count1316 q) 1 1 (meaning1308 q) (meaning1313 q) (meaning1317 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1313 = false ∨ valuation q 1317 = true := counterClause102 (baseVal q)

theorem counterClause103 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1318 = true := by
  have hs : count1316 q = (countLit q [-66, -69, -70]) + (countLit q [-72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-66, -69, -70]) (l₂ := [-72, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1308)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1318)) (countLit q [-66, -69, -70]) (countLit q [-72, -74, -76]) (count1316 q) 1 2 (meaning1308 q) (meaning1314 q) (meaning1318 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1314 = false ∨ valuation q 1318 = true := counterClause103 (baseVal q)

theorem counterClause104 (q : Nat → Bool) : valuationOf q 1300 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1323 = true := by
  have hs : count1322 q = (countLit q [-54, -58, -59, -60, -61, -65]) + (countLit q [-66, -69, -70, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -59, -60, -61, -65]) (l₂ := [-66, -69, -70, -72, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1300)) (literal (valuationOf q) (1316)) (literal (valuationOf q) (1323)) (countLit q [-54, -58, -59, -60, -61, -65]) (countLit q [-66, -69, -70, -72, -74, -76]) (count1322 q) 1 1 (meaning1300 q) (meaning1316 q) (meaning1323 q) hs
  change valuationOf q 1300 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 1300 = false ∨ valuation q 1316 = false ∨ valuation q 1323 = true := counterClause104 (baseVal q)

theorem counterClause105 (q : Nat → Bool) : valuationOf q 1300 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1324 = true := by
  have hs : count1322 q = (countLit q [-54, -58, -59, -60, -61, -65]) + (countLit q [-66, -69, -70, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -59, -60, -61, -65]) (l₂ := [-66, -69, -70, -72, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1300)) (literal (valuationOf q) (1317)) (literal (valuationOf q) (1324)) (countLit q [-54, -58, -59, -60, -61, -65]) (countLit q [-66, -69, -70, -72, -74, -76]) (count1322 q) 1 2 (meaning1300 q) (meaning1317 q) (meaning1324 q) hs
  change valuationOf q 1300 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 1300 = false ∨ valuation q 1317 = false ∨ valuation q 1324 = true := counterClause105 (baseVal q)

theorem counterClause106 (q : Nat → Bool) : valuationOf q 1300 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1325 = true := by
  have hs : count1322 q = (countLit q [-54, -58, -59, -60, -61, -65]) + (countLit q [-66, -69, -70, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -59, -60, -61, -65]) (l₂ := [-66, -69, -70, -72, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1300)) (literal (valuationOf q) (1318)) (literal (valuationOf q) (1325)) (countLit q [-54, -58, -59, -60, -61, -65]) (countLit q [-66, -69, -70, -72, -74, -76]) (count1322 q) 1 3 (meaning1300 q) (meaning1318 q) (meaning1325 q) hs
  change valuationOf q 1300 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 1300 = false ∨ valuation q 1318 = false ∨ valuation q 1325 = true := counterClause106 (baseVal q)

theorem counterClause107 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-78]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1330)) (countLit q [-78]) (countLit q [-82]) (count1330 q) 1 (meaningNeg82 q) (meaning1330 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1330 = true := counterClause107 (baseVal q)

theorem counterClause108 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-78]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1330)) (countLit q [-78]) (countLit q [-82]) (count1330 q) 1 (meaningNeg78 q) (meaning1330 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1330 = true := counterClause108 (baseVal q)

theorem counterClause109 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1331 = true := by
  have hs : count1330 q = (countLit q [-78]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1331)) (countLit q [-78]) (countLit q [-82]) (count1330 q) 1 1 (meaningNeg78 q) (meaningNeg82 q) (meaning1331 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 82 = true ∨ valuation q 1331 = true := counterClause109 (baseVal q)

theorem counterClause110 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1332 = true := by
  have hs : count1332 q = (countLit q [-77]) + (countLit q [-78, -82]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78, -82])
  have hm := merge_right (literal (valuationOf q) (1330)) (literal (valuationOf q) (1332)) (countLit q [-77]) (countLit q [-78, -82]) (count1332 q) 1 (meaning1330 q) (meaning1332 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1332 = true := counterClause110 (baseVal q)

theorem counterClause111 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1333 = true := by
  have hs : count1332 q = (countLit q [-77]) + (countLit q [-78, -82]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78, -82])
  have hm := merge_right (literal (valuationOf q) (1331)) (literal (valuationOf q) (1333)) (countLit q [-77]) (countLit q [-78, -82]) (count1332 q) 2 (meaning1331 q) (meaning1333 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1333 = true := counterClause111 (baseVal q)

theorem counterClause112 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1332 = true := by
  have hs : count1332 q = (countLit q [-77]) + (countLit q [-78, -82]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78, -82])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1332)) (countLit q [-77]) (countLit q [-78, -82]) (count1332 q) 1 (meaningNeg77 q) (meaning1332 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1332 = true := counterClause112 (baseVal q)

theorem counterClause113 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1330 = false ∨ valuationOf q 1333 = true := by
  have hs : count1332 q = (countLit q [-77]) + (countLit q [-78, -82]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78, -82])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1333)) (countLit q [-77]) (countLit q [-78, -82]) (count1332 q) 1 1 (meaningNeg77 q) (meaning1330 q) (meaning1333 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1330 = false ∨ valuation q 1333 = true := counterClause113 (baseVal q)

theorem counterClause114 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1335 = true := by
  have hs : count1335 q = (countLit q [-87]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1335)) (countLit q [-87]) (countLit q [-89]) (count1335 q) 1 (meaningNeg89 q) (meaning1335 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1335 = true := counterClause114 (baseVal q)

theorem counterClause115 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1337 = true := by
  have hs : count1337 q = (countLit q [-84]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-87, -89])
  have hm := merge_right (literal (valuationOf q) (1335)) (literal (valuationOf q) (1337)) (countLit q [-84]) (countLit q [-87, -89]) (count1337 q) 1 (meaning1335 q) (meaning1337 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1337 = true := counterClause115 (baseVal q)

theorem counterClause116 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1337 = true := by
  have hs : count1337 q = (countLit q [-84]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-87, -89])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1337)) (countLit q [-84]) (countLit q [-87, -89]) (count1337 q) 1 (meaningNeg84 q) (meaning1337 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1337 = true := counterClause116 (baseVal q)

theorem counterClause117 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-77, -78, -82]) + (countLit q [-84, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -82]) (l₂ := [-84, -87, -89])
  have hm := merge_right (literal (valuationOf q) (1337)) (literal (valuationOf q) (1340)) (countLit q [-77, -78, -82]) (countLit q [-84, -87, -89]) (count1340 q) 1 (meaning1337 q) (meaning1340 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1340 = true := counterClause117 (baseVal q)

theorem counterClause118 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-77, -78, -82]) + (countLit q [-84, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -82]) (l₂ := [-84, -87, -89])
  have hm := merge_left (literal (valuationOf q) (1332)) (literal (valuationOf q) (1340)) (countLit q [-77, -78, -82]) (countLit q [-84, -87, -89]) (count1340 q) 1 (meaning1332 q) (meaning1340 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1340 = true := counterClause118 (baseVal q)

theorem counterClause119 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-77, -78, -82]) + (countLit q [-84, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -82]) (l₂ := [-84, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1337)) (literal (valuationOf q) (1341)) (countLit q [-77, -78, -82]) (countLit q [-84, -87, -89]) (count1340 q) 1 1 (meaning1332 q) (meaning1337 q) (meaning1341 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1337 = false ∨ valuation q 1341 = true := counterClause119 (baseVal q)

theorem counterClause120 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-77, -78, -82]) + (countLit q [-84, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -82]) (l₂ := [-84, -87, -89])
  have hm := merge_left (literal (valuationOf q) (1333)) (literal (valuationOf q) (1341)) (countLit q [-77, -78, -82]) (countLit q [-84, -87, -89]) (count1340 q) 2 (meaning1333 q) (meaning1341 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1341 = true := counterClause120 (baseVal q)

theorem counterClause121 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1348 = true := by
  have hs : count1348 q = (countLit q [-90]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92, -96])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1348)) (countLit q [-90]) (countLit q [-92, -96]) (count1348 q) 1 (meaningNeg90 q) (meaning1348 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1348 = true := counterClause121 (baseVal q)

theorem counterClause122 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1351 = true := by
  have hs : count1351 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1351)) (countLit q [-98]) (countLit q [-99]) (count1351 q) 1 (meaningNeg99 q) (meaning1351 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1351 = true := counterClause122 (baseVal q)

theorem counterClause123 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1351 = true := by
  have hs : count1351 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1351)) (countLit q [-98]) (countLit q [-99]) (count1351 q) 1 (meaningNeg98 q) (meaning1351 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1351 = true := counterClause123 (baseVal q)

theorem counterClause124 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1353 = true := by
  have hs : count1353 q = (countLit q [-97]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98, -99])
  have hm := merge_right (literal (valuationOf q) (1351)) (literal (valuationOf q) (1353)) (countLit q [-97]) (countLit q [-98, -99]) (count1353 q) 1 (meaning1351 q) (meaning1353 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1353 = true := counterClause124 (baseVal q)

theorem counterClause125 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1353 = true := by
  have hs : count1353 q = (countLit q [-97]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98, -99])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1353)) (countLit q [-97]) (countLit q [-98, -99]) (count1353 q) 1 (meaningNeg97 q) (meaning1353 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1353 = true := counterClause125 (baseVal q)

theorem counterClause126 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-90, -92, -96]) + (countLit q [-97, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96]) (l₂ := [-97, -98, -99])
  have hm := merge_right (literal (valuationOf q) (1353)) (literal (valuationOf q) (1356)) (countLit q [-90, -92, -96]) (countLit q [-97, -98, -99]) (count1356 q) 1 (meaning1353 q) (meaning1356 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1356 = true := counterClause126 (baseVal q)

theorem counterClause127 (q : Nat → Bool) : valuationOf q 1348 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1357 = true := by
  have hs : count1356 q = (countLit q [-90, -92, -96]) + (countLit q [-97, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -96]) (l₂ := [-97, -98, -99])
  have hm := merge_two (literal (valuationOf q) (1348)) (literal (valuationOf q) (1353)) (literal (valuationOf q) (1357)) (countLit q [-90, -92, -96]) (countLit q [-97, -98, -99]) (count1356 q) 1 1 (meaning1348 q) (meaning1353 q) (meaning1357 q) hs
  change valuationOf q 1348 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 1348 = false ∨ valuation q 1353 = false ∨ valuation q 1357 = true := counterClause127 (baseVal q)

theorem counterClause128 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-77, -78, -82, -84, -87, -89]) + (countLit q [-90, -92, -96, -97, -98, -99]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -82, -84, -87, -89]) (l₂ := [-90, -92, -96, -97, -98, -99])
  have hm := merge_right (literal (valuationOf q) (1356)) (literal (valuationOf q) (1362)) (countLit q [-77, -78, -82, -84, -87, -89]) (countLit q [-90, -92, -96, -97, -98, -99]) (count1362 q) 1 (meaning1356 q) (meaning1362 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1362 = true := counterClause128 (baseVal q)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E184.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112184
