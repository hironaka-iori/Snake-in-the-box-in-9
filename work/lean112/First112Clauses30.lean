import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1471 = false ∨ valuation q 1477 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuation q) (1464)) (literal (valuation q) (1471)) (literal (valuation q) (1477)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 2 2 (meaning1464 q) (meaning1471 q) (meaning1477 q) hs
  change valuation q 1464 = false ∨ valuation q 1471 = false ∨ valuation q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1472 = false ∨ valuation q 1478 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuation q) (1464)) (literal (valuation q) (1472)) (literal (valuation q) (1478)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 2 3 (meaning1464 q) (meaning1472 q) (meaning1478 q) hs
  change valuation q 1464 = false ∨ valuation q 1472 = false ∨ valuation q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1473 = false ∨ valuation q 1479 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuation q) (1464)) (literal (valuation q) (1473)) (literal (valuation q) (1479)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 2 4 (meaning1464 q) (meaning1473 q) (meaning1479 q) hs
  change valuation q 1464 = false ∨ valuation q 1473 = false ∨ valuation q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1476 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_left (literal (valuation q) (1465)) (literal (valuation q) (1476)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 3 (meaning1465 q) (meaning1476 q) hs
  change valuation q 1465 = false ∨ valuation q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1470 = false ∨ valuation q 1477 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuation q) (1465)) (literal (valuation q) (1470)) (literal (valuation q) (1477)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 3 1 (meaning1465 q) (meaning1470 q) (meaning1477 q) hs
  change valuation q 1465 = false ∨ valuation q 1470 = false ∨ valuation q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1471 = false ∨ valuation q 1478 = true := by
  have hs : count1474 q = (countLit q [-2, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuation q) (1465)) (literal (valuation q) (1471)) (literal (valuation q) (1478)) (countLit q [-2, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1474 q) 3 2 (meaning1465 q) (meaning1471 q) (meaning1478 q) hs
  change valuation q 1465 = false ∨ valuation q 1471 = false ∨ valuation q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1481 = true := by
  have hs : count1481 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_right (literal (valuation q) (-18)) (literal (valuation q) (1481)) (countLit q [-15]) (countLit q [-18]) (count1481 q) 1 (meaningNeg18 q) (meaning1481 q) hs
  change (! (valuation q 18)) = false ∨ valuation q 1481 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1481 = true := by
  have hs : count1481 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_left (literal (valuation q) (-15)) (literal (valuation q) (1481)) (countLit q [-15]) (countLit q [-18]) (count1481 q) 1 (meaningNeg15 q) (meaning1481 q) hs
  change (! (valuation q 15)) = false ∨ valuation q 1481 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 18 = true ∨ valuation q 1482 = true := by
  have hs : count1481 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_two (literal (valuation q) (-15)) (literal (valuation q) (-18)) (literal (valuation q) (1482)) (countLit q [-15]) (countLit q [-18]) (count1481 q) 1 1 (meaningNeg15 q) (meaningNeg18 q) (meaning1482 q) hs
  change (! (valuation q 15)) = false ∨ (! (valuation q 18)) = false ∨ valuation q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1483 = true := by
  have hs : count1483 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_right (literal (valuation q) (-21)) (literal (valuation q) (1483)) (countLit q [-19]) (countLit q [-21]) (count1483 q) 1 (meaningNeg21 q) (meaning1483 q) hs
  change (! (valuation q 21)) = false ∨ valuation q 1483 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1483 = true := by
  have hs : count1483 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_left (literal (valuation q) (-19)) (literal (valuation q) (1483)) (countLit q [-19]) (countLit q [-21]) (count1483 q) 1 (meaningNeg19 q) (meaning1483 q) hs
  change (! (valuation q 19)) = false ∨ valuation q 1483 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 21 = true ∨ valuation q 1484 = true := by
  have hs : count1483 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_two (literal (valuation q) (-19)) (literal (valuation q) (-21)) (literal (valuation q) (1484)) (countLit q [-19]) (countLit q [-21]) (count1483 q) 1 1 (meaningNeg19 q) (meaningNeg21 q) (meaning1484 q) hs
  change (! (valuation q 19)) = false ∨ (! (valuation q 21)) = false ∨ valuation q 1484 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1485 = true := by
  have hs : count1485 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_right (literal (valuation q) (1483)) (literal (valuation q) (1485)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count1485 q) 1 (meaning1483 q) (meaning1485 q) hs
  change valuation q 1483 = false ∨ valuation q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1486 = true := by
  have hs : count1485 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_right (literal (valuation q) (1484)) (literal (valuation q) (1486)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count1485 q) 2 (meaning1484 q) (meaning1486 q) hs
  change valuation q 1484 = false ∨ valuation q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1485 = true := by
  have hs : count1485 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_left (literal (valuation q) (1481)) (literal (valuation q) (1485)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count1485 q) 1 (meaning1481 q) (meaning1485 q) hs
  change valuation q 1481 = false ∨ valuation q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1483 = false ∨ valuation q 1486 = true := by
  have hs : count1485 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuation q) (1481)) (literal (valuation q) (1483)) (literal (valuation q) (1486)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count1485 q) 1 1 (meaning1481 q) (meaning1483 q) (meaning1486 q) hs
  change valuation q 1481 = false ∨ valuation q 1483 = false ∨ valuation q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1484 = false ∨ valuation q 1487 = true := by
  have hs : count1485 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuation q) (1481)) (literal (valuation q) (1484)) (literal (valuation q) (1487)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count1485 q) 1 2 (meaning1481 q) (meaning1484 q) (meaning1487 q) hs
  change valuation q 1481 = false ∨ valuation q 1484 = false ∨ valuation q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1486 = true := by
  have hs : count1485 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_left (literal (valuation q) (1482)) (literal (valuation q) (1486)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count1485 q) 2 (meaning1482 q) (meaning1486 q) hs
  change valuation q 1482 = false ∨ valuation q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1483 = false ∨ valuation q 1487 = true := by
  have hs : count1485 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuation q) (1482)) (literal (valuation q) (1483)) (literal (valuation q) (1487)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count1485 q) 2 1 (meaning1482 q) (meaning1483 q) (meaning1487 q) hs
  change valuation q 1482 = false ∨ valuation q 1483 = false ∨ valuation q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1484 = false ∨ valuation q 1488 = true := by
  have hs : count1485 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuation q) (1482)) (literal (valuation q) (1484)) (literal (valuation q) (1488)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count1485 q) 2 2 (meaning1482 q) (meaning1484 q) (meaning1488 q) hs
  change valuation q 1482 = false ∨ valuation q 1484 = false ∨ valuation q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1489 = true := by
  have hs : count1489 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_right (literal (valuation q) (-24)) (literal (valuation q) (1489)) (countLit q [-23]) (countLit q [-24]) (count1489 q) 1 (meaningNeg24 q) (meaning1489 q) hs
  change (! (valuation q 24)) = false ∨ valuation q 1489 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1489 = true := by
  have hs : count1489 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_left (literal (valuation q) (-23)) (literal (valuation q) (1489)) (countLit q [-23]) (countLit q [-24]) (count1489 q) 1 (meaningNeg23 q) (meaning1489 q) hs
  change (! (valuation q 23)) = false ∨ valuation q 1489 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 24 = true ∨ valuation q 1490 = true := by
  have hs : count1489 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_two (literal (valuation q) (-23)) (literal (valuation q) (-24)) (literal (valuation q) (1490)) (countLit q [-23]) (countLit q [-24]) (count1489 q) 1 1 (meaningNeg23 q) (meaningNeg24 q) (meaning1490 q) hs
  change (! (valuation q 23)) = false ∨ (! (valuation q 24)) = false ∨ valuation q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1491 = true := by
  have hs : count1491 q = (countLit q [-26]) + (countLit q [-27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-26]) (l₂ := [-27])
  have hm := merge_right (literal (valuation q) (-27)) (literal (valuation q) (1491)) (countLit q [-26]) (countLit q [-27]) (count1491 q) 1 (meaningNeg27 q) (meaning1491 q) hs
  change (! (valuation q 27)) = false ∨ valuation q 1491 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1491 = true := by
  have hs : count1491 q = (countLit q [-26]) + (countLit q [-27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-26]) (l₂ := [-27])
  have hm := merge_left (literal (valuation q) (-26)) (literal (valuation q) (1491)) (countLit q [-26]) (countLit q [-27]) (count1491 q) 1 (meaningNeg26 q) (meaning1491 q) hs
  change (! (valuation q 26)) = false ∨ valuation q 1491 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 27 = true ∨ valuation q 1492 = true := by
  have hs : count1491 q = (countLit q [-26]) + (countLit q [-27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-26]) (l₂ := [-27])
  have hm := merge_two (literal (valuation q) (-26)) (literal (valuation q) (-27)) (literal (valuation q) (1492)) (countLit q [-26]) (countLit q [-27]) (count1491 q) 1 1 (meaningNeg26 q) (meaningNeg27 q) (meaning1492 q) hs
  change (! (valuation q 26)) = false ∨ (! (valuation q 27)) = false ∨ valuation q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1493 = true := by
  have hs : count1493 q = (countLit q [-23, -24]) + (countLit q [-26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-23, -24]) (l₂ := [-26, -27])
  have hm := merge_right (literal (valuation q) (1491)) (literal (valuation q) (1493)) (countLit q [-23, -24]) (countLit q [-26, -27]) (count1493 q) 1 (meaning1491 q) (meaning1493 q) hs
  change valuation q 1491 = false ∨ valuation q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1494 = true := by
  have hs : count1493 q = (countLit q [-23, -24]) + (countLit q [-26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-23, -24]) (l₂ := [-26, -27])
  have hm := merge_right (literal (valuation q) (1492)) (literal (valuation q) (1494)) (countLit q [-23, -24]) (countLit q [-26, -27]) (count1493 q) 2 (meaning1492 q) (meaning1494 q) hs
  change valuation q 1492 = false ∨ valuation q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1493 = true := by
  have hs : count1493 q = (countLit q [-23, -24]) + (countLit q [-26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-23, -24]) (l₂ := [-26, -27])
  have hm := merge_left (literal (valuation q) (1489)) (literal (valuation q) (1493)) (countLit q [-23, -24]) (countLit q [-26, -27]) (count1493 q) 1 (meaning1489 q) (meaning1493 q) hs
  change valuation q 1489 = false ∨ valuation q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1491 = false ∨ valuation q 1494 = true := by
  have hs : count1493 q = (countLit q [-23, -24]) + (countLit q [-26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-23, -24]) (l₂ := [-26, -27])
  have hm := merge_two (literal (valuation q) (1489)) (literal (valuation q) (1491)) (literal (valuation q) (1494)) (countLit q [-23, -24]) (countLit q [-26, -27]) (count1493 q) 1 1 (meaning1489 q) (meaning1491 q) (meaning1494 q) hs
  change valuation q 1489 = false ∨ valuation q 1491 = false ∨ valuation q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1492 = false ∨ valuation q 1495 = true := by
  have hs : count1493 q = (countLit q [-23, -24]) + (countLit q [-26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-23, -24]) (l₂ := [-26, -27])
  have hm := merge_two (literal (valuation q) (1489)) (literal (valuation q) (1492)) (literal (valuation q) (1495)) (countLit q [-23, -24]) (countLit q [-26, -27]) (count1493 q) 1 2 (meaning1489 q) (meaning1492 q) (meaning1495 q) hs
  change valuation q 1489 = false ∨ valuation q 1492 = false ∨ valuation q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1494 = true := by
  have hs : count1493 q = (countLit q [-23, -24]) + (countLit q [-26, -27]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-23, -24]) (l₂ := [-26, -27])
  have hm := merge_left (literal (valuation q) (1490)) (literal (valuation q) (1494)) (countLit q [-23, -24]) (countLit q [-26, -27]) (count1493 q) 2 (meaning1490 q) (meaning1494 q) hs
  change valuation q 1490 = false ∨ valuation q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block30 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.First112
