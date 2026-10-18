import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1386)) (countLit q [-87]) (countLit q [-90]) (count1386 q) 1 (meaningNeg87 q) (meaning1386 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1386 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 90 = true ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (1387)) (countLit q [-87]) (countLit q [-90]) (count1386 q) 1 1 (meaningNeg87 q) (meaningNeg90 q) (meaning1387 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 90 = true ∨ valuation q 1387 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-85]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -90])
  have hm := merge_right (literal (valuationOf q) (1386)) (literal (valuationOf q) (1388)) (countLit q [-85]) (countLit q [-87, -90]) (count1388 q) 1 (meaning1386 q) (meaning1388 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1388 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-85]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -90])
  have hm := merge_right (literal (valuationOf q) (1387)) (literal (valuationOf q) (1389)) (countLit q [-85]) (countLit q [-87, -90]) (count1388 q) 2 (meaning1387 q) (meaning1389 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1389 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-85]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -90])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1388)) (countLit q [-85]) (countLit q [-87, -90]) (count1388 q) 1 (meaningNeg85 q) (meaning1388 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1388 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-85]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -90])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1389)) (countLit q [-85]) (countLit q [-87, -90]) (count1388 q) 1 1 (meaningNeg85 q) (meaning1386 q) (meaning1389 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1386 = false ∨ valuation q 1389 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1391 = true := by
  have hs : count1391 q = (countLit q [-79, -80, -81]) + (countLit q [-85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81]) (l₂ := [-85, -87, -90])
  have hm := merge_left (literal (valuationOf q) (1383)) (literal (valuationOf q) (1391)) (countLit q [-79, -80, -81]) (countLit q [-85, -87, -90]) (count1391 q) 1 (meaning1383 q) (meaning1391 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1391 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1392 = true := by
  have hs : count1391 q = (countLit q [-79, -80, -81]) + (countLit q [-85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81]) (l₂ := [-85, -87, -90])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1392)) (countLit q [-79, -80, -81]) (countLit q [-85, -87, -90]) (count1391 q) 1 1 (meaning1383 q) (meaning1388 q) (meaning1392 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1388 = false ∨ valuation q 1392 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1393 = true := by
  have hs : count1391 q = (countLit q [-79, -80, -81]) + (countLit q [-85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81]) (l₂ := [-85, -87, -90])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1389)) (literal (valuationOf q) (1393)) (countLit q [-79, -80, -81]) (countLit q [-85, -87, -90]) (count1391 q) 1 2 (meaning1383 q) (meaning1389 q) (meaning1393 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1389 = false ∨ valuation q 1393 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1392 = true := by
  have hs : count1391 q = (countLit q [-79, -80, -81]) + (countLit q [-85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81]) (l₂ := [-85, -87, -90])
  have hm := merge_left (literal (valuationOf q) (1384)) (literal (valuationOf q) (1392)) (countLit q [-79, -80, -81]) (countLit q [-85, -87, -90]) (count1391 q) 2 (meaning1384 q) (meaning1392 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1392 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true := by
  have hs : count1391 q = (countLit q [-79, -80, -81]) + (countLit q [-85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81]) (l₂ := [-85, -87, -90])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1393)) (countLit q [-79, -80, -81]) (countLit q [-85, -87, -90]) (count1391 q) 2 1 (meaning1384 q) (meaning1388 q) (meaning1393 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1388 = false ∨ valuation q 1393 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1394 = true := by
  have hs : count1391 q = (countLit q [-79, -80, -81]) + (countLit q [-85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81]) (l₂ := [-85, -87, -90])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1389)) (literal (valuationOf q) (1394)) (countLit q [-79, -80, -81]) (countLit q [-85, -87, -90]) (count1391 q) 2 2 (meaning1384 q) (meaning1389 q) (meaning1394 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1389 = false ∨ valuation q 1394 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1393 = true := by
  have hs : count1391 q = (countLit q [-79, -80, -81]) + (countLit q [-85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81]) (l₂ := [-85, -87, -90])
  have hm := merge_left (literal (valuationOf q) (1385)) (literal (valuationOf q) (1393)) (countLit q [-79, -80, -81]) (countLit q [-85, -87, -90]) (count1391 q) 3 (meaning1385 q) (meaning1393 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1393 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1394 = true := by
  have hs : count1391 q = (countLit q [-79, -80, -81]) + (countLit q [-85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81]) (l₂ := [-85, -87, -90])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1394)) (countLit q [-79, -80, -81]) (countLit q [-85, -87, -90]) (count1391 q) 3 1 (meaning1385 q) (meaning1388 q) (meaning1394 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1388 = false ∨ valuation q 1394 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-93]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-95])
  have hm := merge_right (literal (valuationOf q) (-95)) (literal (valuationOf q) (1397)) (countLit q [-93]) (countLit q [-95]) (count1397 q) 1 (meaningNeg95 q) (meaning1397 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1397 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-93]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1397)) (countLit q [-93]) (countLit q [-95]) (count1397 q) 1 (meaningNeg93 q) (meaning1397 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1397 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-92]) + (countLit q [-93, -95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -95])
  have hm := merge_right (literal (valuationOf q) (1397)) (literal (valuationOf q) (1399)) (countLit q [-92]) (countLit q [-93, -95]) (count1399 q) 1 (meaning1397 q) (meaning1399 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1399 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-92]) + (countLit q [-93, -95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -95])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1399)) (countLit q [-92]) (countLit q [-93, -95]) (count1399 q) 1 (meaningNeg92 q) (meaning1399 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1399 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-92]) + (countLit q [-93, -95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -95])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (1397)) (literal (valuationOf q) (1400)) (countLit q [-92]) (countLit q [-93, -95]) (count1399 q) 1 1 (meaningNeg92 q) (meaning1397 q) (meaning1400 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1397 = false ∨ valuation q 1400 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1402)) (countLit q [-99]) (countLit q [-100]) (count1402 q) 1 (meaningNeg100 q) (meaning1402 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1402 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1402)) (countLit q [-99]) (countLit q [-100]) (count1402 q) 1 (meaningNeg99 q) (meaning1402 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1402 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1403 = true := by
  have hs : count1402 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1403)) (countLit q [-99]) (countLit q [-100]) (count1402 q) 1 1 (meaningNeg99 q) (meaningNeg100 q) (meaning1403 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 1403 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1404 = true := by
  have hs : count1404 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1404)) (countLit q [-101]) (countLit q [-102]) (count1404 q) 1 (meaningNeg102 q) (meaning1404 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1404 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1404 = true := by
  have hs : count1404 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1404)) (countLit q [-101]) (countLit q [-102]) (count1404 q) 1 (meaningNeg101 q) (meaning1404 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1404 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 102 = true ∨ valuationOf q 1405 = true := by
  have hs : count1404 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_two (literal (valuationOf q) (-101)) (literal (valuationOf q) (-102)) (literal (valuationOf q) (1405)) (countLit q [-101]) (countLit q [-102]) (count1404 q) 1 1 (meaningNeg101 q) (meaningNeg102 q) (meaning1405 q) hs
  change (! (valuationOf q 101)) = false ∨ (! (valuationOf q 102)) = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 102 = true ∨ valuation q 1405 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-99, -100]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-101, -102])
  have hm := merge_right (literal (valuationOf q) (1404)) (literal (valuationOf q) (1406)) (countLit q [-99, -100]) (countLit q [-101, -102]) (count1406 q) 1 (meaning1404 q) (meaning1406 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1406 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-99, -100]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-101, -102])
  have hm := merge_right (literal (valuationOf q) (1405)) (literal (valuationOf q) (1407)) (countLit q [-99, -100]) (countLit q [-101, -102]) (count1406 q) 2 (meaning1405 q) (meaning1407 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1407 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-99, -100]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-101, -102])
  have hm := merge_left (literal (valuationOf q) (1402)) (literal (valuationOf q) (1406)) (countLit q [-99, -100]) (countLit q [-101, -102]) (count1406 q) 1 (meaning1402 q) (meaning1406 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1406 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-99, -100]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-101, -102])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1407)) (countLit q [-99, -100]) (countLit q [-101, -102]) (count1406 q) 1 1 (meaning1402 q) (meaning1404 q) (meaning1407 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1404 = false ∨ valuation q 1407 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-99, -100]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-101, -102])
  have hm := merge_left (literal (valuationOf q) (1403)) (literal (valuationOf q) (1407)) (countLit q [-99, -100]) (countLit q [-101, -102]) (count1406 q) 2 (meaning1403 q) (meaning1407 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1407 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-92, -93, -95]) + (countLit q [-99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-99, -100, -101, -102])
  have hm := merge_right (literal (valuationOf q) (1406)) (literal (valuationOf q) (1410)) (countLit q [-92, -93, -95]) (countLit q [-99, -100, -101, -102]) (count1410 q) 1 (meaning1406 q) (meaning1410 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1410 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-92, -93, -95]) + (countLit q [-99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-99, -100, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1399)) (literal (valuationOf q) (1410)) (countLit q [-92, -93, -95]) (countLit q [-99, -100, -101, -102]) (count1410 q) 1 (meaning1399 q) (meaning1410 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1410 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E175.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112175
