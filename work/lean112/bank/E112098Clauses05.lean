import E112098Semantics
import B112E098Inputs
namespace Snake9.Regrowth.E112098
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause161 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1301 = false ∨ valuationOf q 1309 = true := by
  have hs : count1306 q = (countLit q [-50, -52, -54, -57, -58, -60]) + (countLit q [-61, -63, -66, -67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -54, -57, -58, -60]) (l₂ := [-61, -63, -66, -67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1280)) (literal (valuationOf q) (1301)) (literal (valuationOf q) (1309)) (countLit q [-50, -52, -54, -57, -58, -60]) (countLit q [-61, -63, -66, -67, -70, -71, -73]) (count1306 q) 1 3 (meaning1280 q) (meaning1301 q) (meaning1309 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1301 = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1301 = false ∨ valuation q 1309 = true := counterClause161 (baseVal q)

theorem counterClause162 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1317)) (countLit q [-77]) (countLit q [-79]) (count1317 q) 1 (meaningNeg79 q) (meaning1317 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1317 = true := counterClause162 (baseVal q)

theorem counterClause163 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1317)) (countLit q [-77]) (countLit q [-79]) (count1317 q) 1 (meaningNeg77 q) (meaning1317 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1317 = true := counterClause163 (baseVal q)

theorem counterClause164 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1318 = true := by
  have hs : count1317 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1318)) (countLit q [-77]) (countLit q [-79]) (count1317 q) 1 1 (meaningNeg77 q) (meaningNeg79 q) (meaning1318 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 1318 = true := counterClause164 (baseVal q)

theorem counterClause165 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77, -79])
  have hm := merge_right (literal (valuationOf q) (1317)) (literal (valuationOf q) (1319)) (countLit q [-76]) (countLit q [-77, -79]) (count1319 q) 1 (meaning1317 q) (meaning1319 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1319 = true := counterClause165 (baseVal q)

theorem counterClause166 (q : Nat → Bool) : valuationOf q 1318 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77, -79])
  have hm := merge_right (literal (valuationOf q) (1318)) (literal (valuationOf q) (1320)) (countLit q [-76]) (countLit q [-77, -79]) (count1319 q) 2 (meaning1318 q) (meaning1320 q) hs
  change valuationOf q 1318 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 1318 = false ∨ valuation q 1320 = true := counterClause166 (baseVal q)

theorem counterClause167 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77, -79])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1319)) (countLit q [-76]) (countLit q [-77, -79]) (count1319 q) 1 (meaningNeg76 q) (meaning1319 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1319 = true := counterClause167 (baseVal q)

theorem counterClause168 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1318 = false ∨ valuationOf q 1321 = true := by
  have hs : count1319 q = (countLit q [-76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (1318)) (literal (valuationOf q) (1321)) (countLit q [-76]) (countLit q [-77, -79]) (count1319 q) 1 2 (meaningNeg76 q) (meaning1318 q) (meaning1321 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1318 = false ∨ valuation q 1321 = true := counterClause168 (baseVal q)

theorem counterClause169 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1322 = true := by
  have hs : count1322 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1322)) (countLit q [-84]) (countLit q [-85]) (count1322 q) 1 (meaningNeg85 q) (meaning1322 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1322 = true := counterClause169 (baseVal q)

theorem counterClause170 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1322 = true := by
  have hs : count1322 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1322)) (countLit q [-84]) (countLit q [-85]) (count1322 q) 1 (meaningNeg84 q) (meaning1322 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1322 = true := counterClause170 (baseVal q)

theorem counterClause171 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1324 = true := by
  have hs : count1324 q = (countLit q [-82]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84, -85])
  have hm := merge_right (literal (valuationOf q) (1322)) (literal (valuationOf q) (1324)) (countLit q [-82]) (countLit q [-84, -85]) (count1324 q) 1 (meaning1322 q) (meaning1324 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1324 = true := counterClause171 (baseVal q)

theorem counterClause172 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1324 = true := by
  have hs : count1324 q = (countLit q [-82]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84, -85])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1324)) (countLit q [-82]) (countLit q [-84, -85]) (count1324 q) 1 (meaningNeg82 q) (meaning1324 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1324 = true := counterClause172 (baseVal q)

theorem counterClause173 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1322 = false ∨ valuationOf q 1325 = true := by
  have hs : count1324 q = (countLit q [-82]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84, -85])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1325)) (countLit q [-82]) (countLit q [-84, -85]) (count1324 q) 1 1 (meaningNeg82 q) (meaning1322 q) (meaning1325 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1322 = false ∨ valuation q 1325 = true := counterClause173 (baseVal q)

theorem counterClause174 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1327 = true := by
  have hs : count1327 q = (countLit q [-76, -77, -79]) + (countLit q [-82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79]) (l₂ := [-82, -84, -85])
  have hm := merge_right (literal (valuationOf q) (1324)) (literal (valuationOf q) (1327)) (countLit q [-76, -77, -79]) (countLit q [-82, -84, -85]) (count1327 q) 1 (meaning1324 q) (meaning1327 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1327 = true := counterClause174 (baseVal q)

theorem counterClause175 (q : Nat → Bool) : valuationOf q 1325 = false ∨ valuationOf q 1328 = true := by
  have hs : count1327 q = (countLit q [-76, -77, -79]) + (countLit q [-82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79]) (l₂ := [-82, -84, -85])
  have hm := merge_right (literal (valuationOf q) (1325)) (literal (valuationOf q) (1328)) (countLit q [-76, -77, -79]) (countLit q [-82, -84, -85]) (count1327 q) 2 (meaning1325 q) (meaning1328 q) hs
  change valuationOf q 1325 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 1325 = false ∨ valuation q 1328 = true := counterClause175 (baseVal q)

theorem counterClause176 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1327 = true := by
  have hs : count1327 q = (countLit q [-76, -77, -79]) + (countLit q [-82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79]) (l₂ := [-82, -84, -85])
  have hm := merge_left (literal (valuationOf q) (1319)) (literal (valuationOf q) (1327)) (countLit q [-76, -77, -79]) (countLit q [-82, -84, -85]) (count1327 q) 1 (meaning1319 q) (meaning1327 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1327 = true := counterClause176 (baseVal q)

theorem counterClause177 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1328 = true := by
  have hs : count1327 q = (countLit q [-76, -77, -79]) + (countLit q [-82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79]) (l₂ := [-82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1324)) (literal (valuationOf q) (1328)) (countLit q [-76, -77, -79]) (countLit q [-82, -84, -85]) (count1327 q) 1 1 (meaning1319 q) (meaning1324 q) (meaning1328 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1324 = false ∨ valuation q 1328 = true := counterClause177 (baseVal q)

theorem counterClause178 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1325 = false ∨ valuationOf q 1329 = true := by
  have hs : count1327 q = (countLit q [-76, -77, -79]) + (countLit q [-82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79]) (l₂ := [-82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1325)) (literal (valuationOf q) (1329)) (countLit q [-76, -77, -79]) (countLit q [-82, -84, -85]) (count1327 q) 1 2 (meaning1319 q) (meaning1325 q) (meaning1329 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1325 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1325 = false ∨ valuation q 1329 = true := counterClause178 (baseVal q)

theorem counterClause179 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1329 = true := by
  have hs : count1327 q = (countLit q [-76, -77, -79]) + (countLit q [-82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79]) (l₂ := [-82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1320)) (literal (valuationOf q) (1324)) (literal (valuationOf q) (1329)) (countLit q [-76, -77, -79]) (countLit q [-82, -84, -85]) (count1327 q) 2 1 (meaning1320 q) (meaning1324 q) (meaning1329 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1324 = false ∨ valuation q 1329 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1325 = false ∨ valuationOf q 1330 = true := by
  have hs : count1327 q = (countLit q [-76, -77, -79]) + (countLit q [-82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79]) (l₂ := [-82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1320)) (literal (valuationOf q) (1325)) (literal (valuationOf q) (1330)) (countLit q [-76, -77, -79]) (countLit q [-82, -84, -85]) (count1327 q) 2 2 (meaning1320 q) (meaning1325 q) (meaning1330 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1325 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1325 = false ∨ valuation q 1330 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 1321 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1330 = true := by
  have hs : count1327 q = (countLit q [-76, -77, -79]) + (countLit q [-82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-76, -77, -79]) (l₂ := [-82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1321)) (literal (valuationOf q) (1324)) (literal (valuationOf q) (1330)) (countLit q [-76, -77, -79]) (countLit q [-82, -84, -85]) (count1327 q) 3 1 (meaning1321 q) (meaning1324 q) (meaning1330 q) hs
  change valuationOf q 1321 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 1321 = false ∨ valuation q 1324 = false ∨ valuation q 1330 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1333 = true := by
  have hs : count1333 q = (countLit q [-90]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92])
  have hm := merge_right (literal (valuationOf q) (-92)) (literal (valuationOf q) (1333)) (countLit q [-90]) (countLit q [-92]) (count1333 q) 1 (meaningNeg92 q) (meaning1333 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1333 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1333 = true := by
  have hs : count1333 q = (countLit q [-90]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1333)) (countLit q [-90]) (countLit q [-92]) (count1333 q) 1 (meaningNeg90 q) (meaning1333 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1333 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1335 = true := by
  have hs : count1335 q = (countLit q [-89]) + (countLit q [-90, -92]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90, -92])
  have hm := merge_right (literal (valuationOf q) (1333)) (literal (valuationOf q) (1335)) (countLit q [-89]) (countLit q [-90, -92]) (count1335 q) 1 (meaning1333 q) (meaning1335 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1335 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1335 = true := by
  have hs : count1335 q = (countLit q [-89]) + (countLit q [-90, -92]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90, -92])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1335)) (countLit q [-89]) (countLit q [-90, -92]) (count1335 q) 1 (meaningNeg89 q) (meaning1335 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1335 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_right (literal (valuationOf q) (-95)) (literal (valuationOf q) (1338)) (countLit q [-94]) (countLit q [-95]) (count1338 q) 1 (meaningNeg95 q) (meaning1338 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1338 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1338)) (countLit q [-94]) (countLit q [-95]) (count1338 q) 1 (meaningNeg94 q) (meaning1338 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1338 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 95 = true ∨ valuationOf q 1339 = true := by
  have hs : count1338 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-95)) (literal (valuationOf q) (1339)) (countLit q [-94]) (countLit q [-95]) (count1338 q) 1 1 (meaningNeg94 q) (meaningNeg95 q) (meaning1339 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 95)) = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 95 = true ∨ valuation q 1339 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1340)) (countLit q [-98]) (countLit q [-99]) (count1340 q) 1 (meaningNeg99 q) (meaning1340 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1340 = true := counterClause189 (baseVal q)

theorem counterClause190 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1342 = true := by
  have hs : count1342 q = (countLit q [-94, -95]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-98, -99])
  have hm := merge_right (literal (valuationOf q) (1340)) (literal (valuationOf q) (1342)) (countLit q [-94, -95]) (countLit q [-98, -99]) (count1342 q) 1 (meaning1340 q) (meaning1342 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1342 = true := counterClause190 (baseVal q)

theorem counterClause191 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1342 = true := by
  have hs : count1342 q = (countLit q [-94, -95]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-98, -99])
  have hm := merge_left (literal (valuationOf q) (1338)) (literal (valuationOf q) (1342)) (countLit q [-94, -95]) (countLit q [-98, -99]) (count1342 q) 1 (meaning1338 q) (meaning1342 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1342 = true := counterClause191 (baseVal q)

theorem counterClause192 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1343 = true := by
  have hs : count1342 q = (countLit q [-94, -95]) + (countLit q [-98, -99]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-98, -99])
  have hm := merge_two (literal (valuationOf q) (1338)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1343)) (countLit q [-94, -95]) (countLit q [-98, -99]) (count1342 q) 1 1 (meaning1338 q) (meaning1340 q) (meaning1343 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1340 = false ∨ valuation q 1343 = true := counterClause192 (baseVal q)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E098.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112098
