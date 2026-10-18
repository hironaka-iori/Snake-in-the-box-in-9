import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-57]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (1443)) (countLit q [-57]) (countLit q [-58]) (count1443 q) 1 (meaningNeg57 q) (meaning1443 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1443 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 58 = true ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-57]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (-58)) (literal (valuationOf q) (1444)) (countLit q [-57]) (countLit q [-58]) (count1443 q) 1 1 (meaningNeg57 q) (meaningNeg58 q) (meaning1444 q) hs
  change (! (valuationOf q 57)) = false ∨ (! (valuationOf q 58)) = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 58 = true ∨ valuation q 1444 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-55]) + (countLit q [-57, -58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57, -58])
  have hm := merge_right (literal (valuationOf q) (1443)) (literal (valuationOf q) (1445)) (countLit q [-55]) (countLit q [-57, -58]) (count1445 q) 1 (meaning1443 q) (meaning1445 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1445 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-55]) + (countLit q [-57, -58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57, -58])
  have hm := merge_right (literal (valuationOf q) (1444)) (literal (valuationOf q) (1446)) (countLit q [-55]) (countLit q [-57, -58]) (count1445 q) 2 (meaning1444 q) (meaning1446 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1446 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-55]) + (countLit q [-57, -58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57, -58])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1445)) (countLit q [-55]) (countLit q [-57, -58]) (count1445 q) 1 (meaningNeg55 q) (meaning1445 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1445 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1443 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-55]) + (countLit q [-57, -58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57, -58])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1446)) (countLit q [-55]) (countLit q [-57, -58]) (count1445 q) 1 1 (meaningNeg55 q) (meaning1443 q) (meaning1446 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1443 = false ∨ valuation q 1446 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1444 = false ∨ valuationOf q 1447 = true := by
  have hs : count1445 q = (countLit q [-55]) + (countLit q [-57, -58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57, -58])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1447)) (countLit q [-55]) (countLit q [-57, -58]) (count1445 q) 1 2 (meaningNeg55 q) (meaning1444 q) (meaning1447 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1444 = false ∨ valuation q 1447 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1448)) (countLit q [-62]) (countLit q [-63]) (count1448 q) 1 (meaningNeg63 q) (meaning1448 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1448 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (1448)) (countLit q [-62]) (countLit q [-63]) (count1448 q) 1 (meaningNeg62 q) (meaning1448 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1448 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1449)) (countLit q [-62]) (countLit q [-63]) (count1448 q) 1 1 (meaningNeg62 q) (meaningNeg63 q) (meaning1449 q) hs
  change (! (valuationOf q 62)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 63 = true ∨ valuation q 1449 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (1450)) (countLit q [-67]) (countLit q [-69]) (count1450 q) 1 (meaningNeg69 q) (meaning1450 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1450 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1450)) (countLit q [-67]) (countLit q [-69]) (count1450 q) 1 (meaningNeg67 q) (meaning1450 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1450 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 69 = true ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-69)) (literal (valuationOf q) (1451)) (countLit q [-67]) (countLit q [-69]) (count1450 q) 1 1 (meaningNeg67 q) (meaningNeg69 q) (meaning1451 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 69)) = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 69 = true ∨ valuation q 1451 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-62, -63]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-62, -63]) (l₂ := [-67, -69])
  have hm := merge_right (literal (valuationOf q) (1450)) (literal (valuationOf q) (1452)) (countLit q [-62, -63]) (countLit q [-67, -69]) (count1452 q) 1 (meaning1450 q) (meaning1452 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1452 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-62, -63]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-62, -63]) (l₂ := [-67, -69])
  have hm := merge_right (literal (valuationOf q) (1451)) (literal (valuationOf q) (1453)) (countLit q [-62, -63]) (countLit q [-67, -69]) (count1452 q) 2 (meaning1451 q) (meaning1453 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1453 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-62, -63]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-62, -63]) (l₂ := [-67, -69])
  have hm := merge_left (literal (valuationOf q) (1448)) (literal (valuationOf q) (1452)) (countLit q [-62, -63]) (countLit q [-67, -69]) (count1452 q) 1 (meaning1448 q) (meaning1452 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1452 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-62, -63]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-62, -63]) (l₂ := [-67, -69])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1453)) (countLit q [-62, -63]) (countLit q [-67, -69]) (count1452 q) 1 1 (meaning1448 q) (meaning1450 q) (meaning1453 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1450 = false ∨ valuation q 1453 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-62, -63]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-62, -63]) (l₂ := [-67, -69])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1454)) (countLit q [-62, -63]) (countLit q [-67, -69]) (count1452 q) 1 2 (meaning1448 q) (meaning1451 q) (meaning1454 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1451 = false ∨ valuation q 1454 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-62, -63]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-62, -63]) (l₂ := [-67, -69])
  have hm := merge_left (literal (valuationOf q) (1449)) (literal (valuationOf q) (1453)) (countLit q [-62, -63]) (countLit q [-67, -69]) (count1452 q) 2 (meaning1449 q) (meaning1453 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1453 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-62, -63]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-62, -63]) (l₂ := [-67, -69])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1454)) (countLit q [-62, -63]) (countLit q [-67, -69]) (count1452 q) 2 1 (meaning1449 q) (meaning1450 q) (meaning1454 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1450 = false ∨ valuation q 1454 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-55, -57, -58]) + (countLit q [-62, -63, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58]) (l₂ := [-62, -63, -67, -69])
  have hm := merge_right (literal (valuationOf q) (1452)) (literal (valuationOf q) (1456)) (countLit q [-55, -57, -58]) (countLit q [-62, -63, -67, -69]) (count1456 q) 1 (meaning1452 q) (meaning1456 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1456 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-55, -57, -58]) + (countLit q [-62, -63, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58]) (l₂ := [-62, -63, -67, -69])
  have hm := merge_right (literal (valuationOf q) (1453)) (literal (valuationOf q) (1457)) (countLit q [-55, -57, -58]) (countLit q [-62, -63, -67, -69]) (count1456 q) 2 (meaning1453 q) (meaning1457 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1457 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1458 = true := by
  have hs : count1456 q = (countLit q [-55, -57, -58]) + (countLit q [-62, -63, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58]) (l₂ := [-62, -63, -67, -69])
  have hm := merge_right (literal (valuationOf q) (1454)) (literal (valuationOf q) (1458)) (countLit q [-55, -57, -58]) (countLit q [-62, -63, -67, -69]) (count1456 q) 3 (meaning1454 q) (meaning1458 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1458 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-55, -57, -58]) + (countLit q [-62, -63, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58]) (l₂ := [-62, -63, -67, -69])
  have hm := merge_left (literal (valuationOf q) (1445)) (literal (valuationOf q) (1456)) (countLit q [-55, -57, -58]) (countLit q [-62, -63, -67, -69]) (count1456 q) 1 (meaning1445 q) (meaning1456 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1456 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-55, -57, -58]) + (countLit q [-62, -63, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58]) (l₂ := [-62, -63, -67, -69])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1457)) (countLit q [-55, -57, -58]) (countLit q [-62, -63, -67, -69]) (count1456 q) 1 1 (meaning1445 q) (meaning1452 q) (meaning1457 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1452 = false ∨ valuation q 1457 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1458 = true := by
  have hs : count1456 q = (countLit q [-55, -57, -58]) + (countLit q [-62, -63, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58]) (l₂ := [-62, -63, -67, -69])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1458)) (countLit q [-55, -57, -58]) (countLit q [-62, -63, -67, -69]) (count1456 q) 1 2 (meaning1445 q) (meaning1453 q) (meaning1458 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1453 = false ∨ valuation q 1458 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1459 = true := by
  have hs : count1456 q = (countLit q [-55, -57, -58]) + (countLit q [-62, -63, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58]) (l₂ := [-62, -63, -67, -69])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1459)) (countLit q [-55, -57, -58]) (countLit q [-62, -63, -67, -69]) (count1456 q) 1 3 (meaning1445 q) (meaning1454 q) (meaning1459 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1454 = false ∨ valuation q 1459 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-55, -57, -58]) + (countLit q [-62, -63, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58]) (l₂ := [-62, -63, -67, -69])
  have hm := merge_left (literal (valuationOf q) (1446)) (literal (valuationOf q) (1457)) (countLit q [-55, -57, -58]) (countLit q [-62, -63, -67, -69]) (count1456 q) 2 (meaning1446 q) (meaning1457 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1457 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1458 = true := by
  have hs : count1456 q = (countLit q [-55, -57, -58]) + (countLit q [-62, -63, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58]) (l₂ := [-62, -63, -67, -69])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1458)) (countLit q [-55, -57, -58]) (countLit q [-62, -63, -67, -69]) (count1456 q) 2 1 (meaning1446 q) (meaning1452 q) (meaning1458 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1452 = false ∨ valuation q 1458 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1459 = true := by
  have hs : count1456 q = (countLit q [-55, -57, -58]) + (countLit q [-62, -63, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58]) (l₂ := [-62, -63, -67, -69])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1459)) (countLit q [-55, -57, -58]) (countLit q [-62, -63, -67, -69]) (count1456 q) 2 2 (meaning1446 q) (meaning1453 q) (meaning1459 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1453 = false ∨ valuation q 1459 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1460 = true := by
  have hs : count1456 q = (countLit q [-55, -57, -58]) + (countLit q [-62, -63, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58]) (l₂ := [-62, -63, -67, -69])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1460)) (countLit q [-55, -57, -58]) (countLit q [-62, -63, -67, -69]) (count1456 q) 2 3 (meaning1446 q) (meaning1454 q) (meaning1460 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1454 = false ∨ valuation q 1460 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1459 = true := by
  have hs : count1456 q = (countLit q [-55, -57, -58]) + (countLit q [-62, -63, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58]) (l₂ := [-62, -63, -67, -69])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1459)) (countLit q [-55, -57, -58]) (countLit q [-62, -63, -67, -69]) (count1456 q) 3 1 (meaning1447 q) (meaning1452 q) (meaning1459 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1452 = false ∨ valuation q 1459 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E161.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112161
