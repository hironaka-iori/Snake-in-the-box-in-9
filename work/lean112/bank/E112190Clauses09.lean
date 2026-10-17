import E112190Semantics
import B112E190Inputs
namespace Snake9.Regrowth.E112190
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1405 = true := by
  have hs : count1405 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1405)) (countLit q [-64]) (countLit q [-65]) (count1405 q) 1 (meaningNeg64 q) (meaning1405 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1405 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1407 = true := by
  have hs : count1407 q = (countLit q [-62]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64, -65])
  have hm := merge_right (literal (valuationOf q) (1405)) (literal (valuationOf q) (1407)) (countLit q [-62]) (countLit q [-64, -65]) (count1407 q) 1 (meaning1405 q) (meaning1407 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1407 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1407 = true := by
  have hs : count1407 q = (countLit q [-62]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64, -65])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (1407)) (countLit q [-62]) (countLit q [-64, -65]) (count1407 q) 1 (meaningNeg62 q) (meaning1407 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1407 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1405 = false ∨ valuationOf q 1408 = true := by
  have hs : count1407 q = (countLit q [-62]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64, -65])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (1405)) (literal (valuationOf q) (1408)) (countLit q [-62]) (countLit q [-64, -65]) (count1407 q) 1 1 (meaningNeg62 q) (meaning1405 q) (meaning1408 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1405 = false ∨ valuation q 1408 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-56, -57, -59]) + (countLit q [-62, -64, -65]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59]) (l₂ := [-62, -64, -65])
  have hm := merge_right (literal (valuationOf q) (1407)) (literal (valuationOf q) (1410)) (countLit q [-56, -57, -59]) (countLit q [-62, -64, -65]) (count1410 q) 1 (meaning1407 q) (meaning1410 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1410 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-56, -57, -59]) + (countLit q [-62, -64, -65]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59]) (l₂ := [-62, -64, -65])
  have hm := merge_right (literal (valuationOf q) (1408)) (literal (valuationOf q) (1411)) (countLit q [-56, -57, -59]) (countLit q [-62, -64, -65]) (count1410 q) 2 (meaning1408 q) (meaning1411 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1411 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-56, -57, -59]) + (countLit q [-62, -64, -65]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59]) (l₂ := [-62, -64, -65])
  have hm := merge_left (literal (valuationOf q) (1402)) (literal (valuationOf q) (1410)) (countLit q [-56, -57, -59]) (countLit q [-62, -64, -65]) (count1410 q) 1 (meaning1402 q) (meaning1410 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1410 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-56, -57, -59]) + (countLit q [-62, -64, -65]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59]) (l₂ := [-62, -64, -65])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1411)) (countLit q [-56, -57, -59]) (countLit q [-62, -64, -65]) (count1410 q) 1 1 (meaning1402 q) (meaning1407 q) (meaning1411 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1407 = false ∨ valuation q 1411 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-56, -57, -59]) + (countLit q [-62, -64, -65]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59]) (l₂ := [-62, -64, -65])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1412)) (countLit q [-56, -57, -59]) (countLit q [-62, -64, -65]) (count1410 q) 1 2 (meaning1402 q) (meaning1408 q) (meaning1412 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1408 = false ∨ valuation q 1412 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1416 = true := by
  have hs : count1416 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1416)) (countLit q [-69]) (countLit q [-71]) (count1416 q) 1 (meaningNeg71 q) (meaning1416 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1416 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1416 = true := by
  have hs : count1416 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1416)) (countLit q [-69]) (countLit q [-71]) (count1416 q) 1 (meaningNeg69 q) (meaning1416 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1416 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-66]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-69, -71])
  have hm := merge_right (literal (valuationOf q) (1416)) (literal (valuationOf q) (1418)) (countLit q [-66]) (countLit q [-69, -71]) (count1418 q) 1 (meaning1416 q) (meaning1418 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1418 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-66]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-69, -71])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1418)) (countLit q [-66]) (countLit q [-69, -71]) (count1418 q) 1 (meaningNeg66 q) (meaning1418 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1418 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1421)) (countLit q [-72]) (countLit q [-74]) (count1421 q) 1 (meaningNeg72 q) (meaning1421 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1421 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 74 = true ∨ valuationOf q 1422 = true := by
  have hs : count1421 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (1422)) (countLit q [-72]) (countLit q [-74]) (count1421 q) 1 1 (meaningNeg72 q) (meaningNeg74 q) (meaning1422 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 74 = true ∨ valuation q 1422 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1423)) (countLit q [-78]) (countLit q [-80]) (count1423 q) 1 (meaningNeg80 q) (meaning1423 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1423 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1423)) (countLit q [-78]) (countLit q [-80]) (count1423 q) 1 (meaningNeg78 q) (meaning1423 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1423 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 80 = true ∨ valuationOf q 1424 = true := by
  have hs : count1423 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (1424)) (countLit q [-78]) (countLit q [-80]) (count1423 q) 1 1 (meaningNeg78 q) (meaningNeg80 q) (meaning1424 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 80 = true ∨ valuation q 1424 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1425 = true := by
  have hs : count1425 q = (countLit q [-72, -74]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-78, -80])
  have hm := merge_right (literal (valuationOf q) (1423)) (literal (valuationOf q) (1425)) (countLit q [-72, -74]) (countLit q [-78, -80]) (count1425 q) 1 (meaning1423 q) (meaning1425 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1425 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-72, -74]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-78, -80])
  have hm := merge_right (literal (valuationOf q) (1424)) (literal (valuationOf q) (1426)) (countLit q [-72, -74]) (countLit q [-78, -80]) (count1425 q) 2 (meaning1424 q) (meaning1426 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1426 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1425 = true := by
  have hs : count1425 q = (countLit q [-72, -74]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-78, -80])
  have hm := merge_left (literal (valuationOf q) (1421)) (literal (valuationOf q) (1425)) (countLit q [-72, -74]) (countLit q [-78, -80]) (count1425 q) 1 (meaning1421 q) (meaning1425 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1425 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-72, -74]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-78, -80])
  have hm := merge_two (literal (valuationOf q) (1421)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1426)) (countLit q [-72, -74]) (countLit q [-78, -80]) (count1425 q) 1 1 (meaning1421 q) (meaning1423 q) (meaning1426 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1423 = false ∨ valuation q 1426 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-72, -74]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-78, -80])
  have hm := merge_left (literal (valuationOf q) (1422)) (literal (valuationOf q) (1426)) (countLit q [-72, -74]) (countLit q [-78, -80]) (count1425 q) 2 (meaning1422 q) (meaning1426 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1426 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1429 = true := by
  have hs : count1429 q = (countLit q [-66, -69, -71]) + (countLit q [-72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-66, -69, -71]) (l₂ := [-72, -74, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1425)) (literal (valuationOf q) (1429)) (countLit q [-66, -69, -71]) (countLit q [-72, -74, -78, -80]) (count1429 q) 1 (meaning1425 q) (meaning1429 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1429 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1430 = true := by
  have hs : count1429 q = (countLit q [-66, -69, -71]) + (countLit q [-72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-66, -69, -71]) (l₂ := [-72, -74, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1426)) (literal (valuationOf q) (1430)) (countLit q [-66, -69, -71]) (countLit q [-72, -74, -78, -80]) (count1429 q) 2 (meaning1426 q) (meaning1430 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1430 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1429 = true := by
  have hs : count1429 q = (countLit q [-66, -69, -71]) + (countLit q [-72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-66, -69, -71]) (l₂ := [-72, -74, -78, -80])
  have hm := merge_left (literal (valuationOf q) (1418)) (literal (valuationOf q) (1429)) (countLit q [-66, -69, -71]) (countLit q [-72, -74, -78, -80]) (count1429 q) 1 (meaning1418 q) (meaning1429 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1429 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1430 = true := by
  have hs : count1429 q = (countLit q [-66, -69, -71]) + (countLit q [-72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-66, -69, -71]) (l₂ := [-72, -74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1425)) (literal (valuationOf q) (1430)) (countLit q [-66, -69, -71]) (countLit q [-72, -74, -78, -80]) (count1429 q) 1 1 (meaning1418 q) (meaning1425 q) (meaning1430 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1425 = false ∨ valuation q 1430 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1431 = true := by
  have hs : count1429 q = (countLit q [-66, -69, -71]) + (countLit q [-72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-66, -69, -71]) (l₂ := [-72, -74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1426)) (literal (valuationOf q) (1431)) (countLit q [-66, -69, -71]) (countLit q [-72, -74, -78, -80]) (count1429 q) 1 2 (meaning1418 q) (meaning1426 q) (meaning1431 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1426 = false ∨ valuation q 1431 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1436 = true := by
  have hs : count1436 q = (countLit q [-56, -57, -59, -62, -64, -65]) + (countLit q [-66, -69, -71, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65]) (l₂ := [-66, -69, -71, -72, -74, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1429)) (literal (valuationOf q) (1436)) (countLit q [-56, -57, -59, -62, -64, -65]) (countLit q [-66, -69, -71, -72, -74, -78, -80]) (count1436 q) 1 (meaning1429 q) (meaning1436 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1436 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1437 = true := by
  have hs : count1436 q = (countLit q [-56, -57, -59, -62, -64, -65]) + (countLit q [-66, -69, -71, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65]) (l₂ := [-66, -69, -71, -72, -74, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1430)) (literal (valuationOf q) (1437)) (countLit q [-56, -57, -59, -62, -64, -65]) (countLit q [-66, -69, -71, -72, -74, -78, -80]) (count1436 q) 2 (meaning1430 q) (meaning1437 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1437 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1438 = true := by
  have hs : count1436 q = (countLit q [-56, -57, -59, -62, -64, -65]) + (countLit q [-66, -69, -71, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65]) (l₂ := [-66, -69, -71, -72, -74, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1431)) (literal (valuationOf q) (1438)) (countLit q [-56, -57, -59, -62, -64, -65]) (countLit q [-66, -69, -71, -72, -74, -78, -80]) (count1436 q) 3 (meaning1431 q) (meaning1438 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1438 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1437 = true := by
  have hs : count1436 q = (countLit q [-56, -57, -59, -62, -64, -65]) + (countLit q [-66, -69, -71, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-56, -57, -59, -62, -64, -65]) (l₂ := [-66, -69, -71, -72, -74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1410)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1437)) (countLit q [-56, -57, -59, -62, -64, -65]) (countLit q [-66, -69, -71, -72, -74, -78, -80]) (count1436 q) 1 1 (meaning1410 q) (meaning1429 q) (meaning1437 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1429 = false ∨ valuation q 1437 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E190.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112190
