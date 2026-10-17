import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 968 = false ∨ valuationOf q 973 = true := by
  have hs : count972 q = (countLit q [-95, -97, -100, -102]) + (countLit q [-103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -100, -102]) (l₂ := [-103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (968)) (literal (valuationOf q) (973)) (countLit q [-95, -97, -100, -102]) (countLit q [-103, -105, -108, -110]) (count972 q) 1 1 (meaning960 q) (meaning968 q) (meaning973 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 968 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 968 = false ∨ valuation q 973 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 980 = true := by
  have hs : count980 q = (countLit q [-81, -83, -87, -88, -90, -92, -94]) + (countLit q [-95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-81, -83, -87, -88, -90, -92, -94]) (l₂ := [-95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_left (literal (valuationOf q) (949)) (literal (valuationOf q) (980)) (countLit q [-81, -83, -87, -88, -90, -92, -94]) (countLit q [-95, -97, -100, -102, -103, -105, -108, -110]) (count980 q) 1 (meaning949 q) (meaning980 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 980 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 972 = false ∨ valuationOf q 981 = true := by
  have hs : count980 q = (countLit q [-81, -83, -87, -88, -90, -92, -94]) + (countLit q [-95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-81, -83, -87, -88, -90, -92, -94]) (l₂ := [-95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (972)) (literal (valuationOf q) (981)) (countLit q [-81, -83, -87, -88, -90, -92, -94]) (countLit q [-95, -97, -100, -102, -103, -105, -108, -110]) (count980 q) 1 1 (meaning949 q) (meaning972 q) (meaning981 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 972 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 972 = false ∨ valuation q 981 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 973 = false ∨ valuationOf q 982 = true := by
  have hs : count980 q = (countLit q [-81, -83, -87, -88, -90, -92, -94]) + (countLit q [-95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-81, -83, -87, -88, -90, -92, -94]) (l₂ := [-95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (973)) (literal (valuationOf q) (982)) (countLit q [-81, -83, -87, -88, -90, -92, -94]) (countLit q [-95, -97, -100, -102, -103, -105, -108, -110]) (count980 q) 1 2 (meaning949 q) (meaning973 q) (meaning982 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 973 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 973 = false ∨ valuation q 982 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 972 = false ∨ valuationOf q 982 = true := by
  have hs : count980 q = (countLit q [-81, -83, -87, -88, -90, -92, -94]) + (countLit q [-95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-81, -83, -87, -88, -90, -92, -94]) (l₂ := [-95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (950)) (literal (valuationOf q) (972)) (literal (valuationOf q) (982)) (countLit q [-81, -83, -87, -88, -90, -92, -94]) (countLit q [-95, -97, -100, -102, -103, -105, -108, -110]) (count980 q) 2 1 (meaning950 q) (meaning972 q) (meaning982 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 972 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 972 = false ∨ valuation q 982 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 972 = false ∨ valuationOf q 983 = true := by
  have hs : count980 q = (countLit q [-81, -83, -87, -88, -90, -92, -94]) + (countLit q [-95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-81, -83, -87, -88, -90, -92, -94]) (l₂ := [-95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (951)) (literal (valuationOf q) (972)) (literal (valuationOf q) (983)) (countLit q [-81, -83, -87, -88, -90, -92, -94]) (countLit q [-95, -97, -100, -102, -103, -105, -108, -110]) (count980 q) 3 1 (meaning951 q) (meaning972 q) (meaning983 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 972 = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 972 = false ∨ valuation q 983 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 981 = false ∨ valuationOf q 998 = true := by
  have hs : count995 q = (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) + (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (l₂ := [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (981)) (literal (valuationOf q) (998)) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count995 q) 2 2 (meaning923 q) (meaning981 q) (meaning998 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 981 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 981 = false ∨ valuation q 998 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1000 = true := by
  have hs : count995 q = (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) + (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (l₂ := [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1000)) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count995 q) 2 4 (meaning923 q) (meaning983 q) (meaning1000 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 983 = false ∨ valuation q 1000 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 981 = false ∨ valuationOf q 999 = true := by
  have hs : count995 q = (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) + (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (l₂ := [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (981)) (literal (valuationOf q) (999)) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count995 q) 3 2 (meaning924 q) (meaning981 q) (meaning999 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 981 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 981 = false ∨ valuation q 999 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1000 = true := by
  have hs : count995 q = (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) + (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (l₂ := [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1000)) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count995 q) 3 3 (meaning924 q) (meaning982 q) (meaning1000 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 982 = false ∨ valuation q 1000 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1001 = true := by
  have hs : count995 q = (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) + (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (l₂ := [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1001)) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count995 q) 3 4 (meaning924 q) (meaning983 q) (meaning1001 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 983 = false ∨ valuation q 1001 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1000 = true := by
  have hs : count995 q = (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) + (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (l₂ := [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1000)) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count995 q) 4 2 (meaning925 q) (meaning981 q) (meaning1000 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 981 = false ∨ valuation q 1000 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1001 = true := by
  have hs : count995 q = (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) + (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (l₂ := [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1001)) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count995 q) 4 3 (meaning925 q) (meaning982 q) (meaning1001 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 982 = false ∨ valuation q 1001 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1002 = true := by
  have hs : count995 q = (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) + (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (l₂ := [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1002)) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count995 q) 4 4 (meaning925 q) (meaning983 q) (meaning1002 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 983 = false ∨ valuation q 1002 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1001 = true := by
  have hs : count995 q = (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) + (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (l₂ := [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (926)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1001)) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count995 q) 5 2 (meaning926 q) (meaning981 q) (meaning1001 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 981 = false ∨ valuation q 1001 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1002 = true := by
  have hs : count995 q = (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) + (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (l₂ := [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (926)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1002)) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count995 q) 5 3 (meaning926 q) (meaning982 q) (meaning1002 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 982 = false ∨ valuation q 1002 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 927 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1002 = true := by
  have hs : count995 q = (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) + (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (l₂ := [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (927)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1002)) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count995 q) 6 2 (meaning927 q) (meaning981 q) (meaning1002 q) hs
  change valuationOf q 927 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 927 = false ∨ valuation q 981 = false ∨ valuation q 1002 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1002 = true := by
  have hs : count995 q = (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) + (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (l₂ := [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (928)) (literal (valuationOf q) (980)) (literal (valuationOf q) (1002)) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count995 q) 7 1 (meaning928 q) (meaning980 q) (meaning1002 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 980 = false ∨ valuation q 1002 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1003 = true := by
  have hs : count995 q = (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) + (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (l₂ := [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (928)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1003)) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80]) (countLit q [-81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count995 q) 7 2 (meaning928 q) (meaning981 q) (meaning1003 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 981 = false ∨ valuation q 1003 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 1003 = false ∨ valuationOf q 1028 = true := by
  have hs : count1012 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) + (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (l₂ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (1003)) (literal (valuationOf q) (1028)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count1012 q) 8 9 (meaning872 q) (meaning1003 q) (meaning1028 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 1003 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 1003 = false ∨ valuation q 1028 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1028 = true := by
  have hs : count1012 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) + (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (l₂ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (873)) (literal (valuationOf q) (1002)) (literal (valuationOf q) (1028)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count1012 q) 9 8 (meaning873 q) (meaning1002 q) (meaning1028 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 1002 = false ∨ valuation q 1028 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 1001 = false ∨ valuationOf q 1028 = true := by
  have hs : count1012 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) + (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (l₂ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (874)) (literal (valuationOf q) (1001)) (literal (valuationOf q) (1028)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count1012 q) 10 7 (meaning874 q) (meaning1001 q) (meaning1028 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 1001 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 1001 = false ∨ valuation q 1028 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1028 = true := by
  have hs : count1012 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) + (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (l₂ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (1000)) (literal (valuationOf q) (1028)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count1012 q) 11 6 (meaning875 q) (meaning1000 q) (meaning1028 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 1000 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 1000 = false ∨ valuation q 1028 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1028 = true := by
  have hs : count1012 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) + (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (l₂ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (999)) (literal (valuationOf q) (1028)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count1012 q) 12 5 (meaning876 q) (meaning999 q) (meaning1028 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 999 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 999 = false ∨ valuation q 1028 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1028 = true := by
  have hs : count1012 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) + (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (l₂ := [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (998)) (literal (valuationOf q) (1028)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (countLit q [-55, -57, -60, -62, -63, -65, -68, -70, -71, -73, -76, -77, -79, -80, -81, -83, -87, -88, -90, -92, -94, -95, -97, -100, -102, -103, -105, -108, -110]) (count1012 q) 13 4 (meaning877 q) (meaning998 q) (meaning1028 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 998 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 998 = false ∨ valuation q 1028 = true := counterClause601 (baseVal q)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 1028 = false := by
  rw [value1028]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1012 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause603 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1327 = true := by
  have hs : count1327 q = (countLit q [-2]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -7])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1327)) (countLit q [-2]) (countLit q [-3, -7]) (count1327 q) 1 (meaningNeg2 q) (meaning1327 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1327 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-10]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1330)) (countLit q [-10]) (countLit q [-13]) (count1330 q) 1 (meaningNeg13 q) (meaning1330 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1330 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-10]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1330)) (countLit q [-10]) (countLit q [-13]) (count1330 q) 1 (meaningNeg10 q) (meaning1330 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1330 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1332 = true := by
  have hs : count1332 q = (countLit q [-8]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -13])
  have hm := merge_right (literal (valuationOf q) (1330)) (literal (valuationOf q) (1332)) (countLit q [-8]) (countLit q [-10, -13]) (count1332 q) 1 (meaning1330 q) (meaning1332 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1332 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1332 = true := by
  have hs : count1332 q = (countLit q [-8]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -13])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1332)) (countLit q [-8]) (countLit q [-10, -13]) (count1332 q) 1 (meaningNeg8 q) (meaning1332 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1332 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1335 = true := by
  have hs : count1335 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -10, -13])
  have hm := merge_left (literal (valuationOf q) (1327)) (literal (valuationOf q) (1335)) (countLit q [-2, -3, -7]) (countLit q [-8, -10, -13]) (count1335 q) 1 (meaning1327 q) (meaning1335 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1335 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E123.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112123
