import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 77 = true ∨ valuationOf q 952 = true := by
  have hs : count951 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (952)) (countLit q [-76]) (countLit q [-77]) (count951 q) 1 1 (meaningNeg76 q) (meaningNeg77 q) (meaning952 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 77 = true ∨ valuation q 952 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 953 = true := by
  have hs : count953 q = (countLit q [-70, -73]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-76, -77])
  have hm := merge_right (literal (valuationOf q) (951)) (literal (valuationOf q) (953)) (countLit q [-70, -73]) (countLit q [-76, -77]) (count953 q) 1 (meaning951 q) (meaning953 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 953 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-70, -73]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-76, -77])
  have hm := merge_right (literal (valuationOf q) (952)) (literal (valuationOf q) (954)) (countLit q [-70, -73]) (countLit q [-76, -77]) (count953 q) 2 (meaning952 q) (meaning954 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 954 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 953 = true := by
  have hs : count953 q = (countLit q [-70, -73]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-76, -77])
  have hm := merge_left (literal (valuationOf q) (949)) (literal (valuationOf q) (953)) (countLit q [-70, -73]) (countLit q [-76, -77]) (count953 q) 1 (meaning949 q) (meaning953 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 953 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 951 = false ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-70, -73]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-76, -77])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (951)) (literal (valuationOf q) (954)) (countLit q [-70, -73]) (countLit q [-76, -77]) (count953 q) 1 1 (meaning949 q) (meaning951 q) (meaning954 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 951 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 951 = false ∨ valuation q 954 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 952 = false ∨ valuationOf q 955 = true := by
  have hs : count953 q = (countLit q [-70, -73]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-76, -77])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (952)) (literal (valuationOf q) (955)) (countLit q [-70, -73]) (countLit q [-76, -77]) (count953 q) 1 2 (meaning949 q) (meaning952 q) (meaning955 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 952 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 952 = false ∨ valuation q 955 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-70, -73]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-76, -77])
  have hm := merge_left (literal (valuationOf q) (950)) (literal (valuationOf q) (954)) (countLit q [-70, -73]) (countLit q [-76, -77]) (count953 q) 2 (meaning950 q) (meaning954 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 954 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 951 = false ∨ valuationOf q 955 = true := by
  have hs : count953 q = (countLit q [-70, -73]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-76, -77])
  have hm := merge_two (literal (valuationOf q) (950)) (literal (valuationOf q) (951)) (literal (valuationOf q) (955)) (countLit q [-70, -73]) (countLit q [-76, -77]) (count953 q) 2 1 (meaning950 q) (meaning951 q) (meaning955 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 951 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 951 = false ∨ valuation q 955 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 952 = false ∨ valuationOf q 956 = true := by
  have hs : count953 q = (countLit q [-70, -73]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-76, -77])
  have hm := merge_two (literal (valuationOf q) (950)) (literal (valuationOf q) (952)) (literal (valuationOf q) (956)) (countLit q [-70, -73]) (countLit q [-76, -77]) (count953 q) 2 2 (meaning950 q) (meaning952 q) (meaning956 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 952 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 952 = false ∨ valuation q 956 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 957 = true := by
  have hs : count957 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (957)) (countLit q [-78]) (countLit q [-80]) (count957 q) 1 (meaningNeg80 q) (meaning957 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 957 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 957 = true := by
  have hs : count957 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (957)) (countLit q [-78]) (countLit q [-80]) (count957 q) 1 (meaningNeg78 q) (meaning957 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 957 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 80 = true ∨ valuationOf q 958 = true := by
  have hs : count957 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (958)) (countLit q [-78]) (countLit q [-80]) (count957 q) 1 1 (meaningNeg78 q) (meaningNeg80 q) (meaning958 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 80 = true ∨ valuation q 958 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 959 = true := by
  have hs : count959 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (959)) (countLit q [-84]) (countLit q [-85]) (count959 q) 1 (meaningNeg85 q) (meaning959 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 959 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 959 = true := by
  have hs : count959 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (959)) (countLit q [-84]) (countLit q [-85]) (count959 q) 1 (meaningNeg84 q) (meaning959 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 959 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 85 = true ∨ valuationOf q 960 = true := by
  have hs : count959 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (960)) (countLit q [-84]) (countLit q [-85]) (count959 q) 1 1 (meaningNeg84 q) (meaningNeg85 q) (meaning960 q) hs
  change (! (valuationOf q 84)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 85 = true ∨ valuation q 960 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 961 = true := by
  have hs : count961 q = (countLit q [-78, -80]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-84, -85])
  have hm := merge_right (literal (valuationOf q) (959)) (literal (valuationOf q) (961)) (countLit q [-78, -80]) (countLit q [-84, -85]) (count961 q) 1 (meaning959 q) (meaning961 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 961 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 962 = true := by
  have hs : count961 q = (countLit q [-78, -80]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-84, -85])
  have hm := merge_right (literal (valuationOf q) (960)) (literal (valuationOf q) (962)) (countLit q [-78, -80]) (countLit q [-84, -85]) (count961 q) 2 (meaning960 q) (meaning962 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 962 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 961 = true := by
  have hs : count961 q = (countLit q [-78, -80]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-84, -85])
  have hm := merge_left (literal (valuationOf q) (957)) (literal (valuationOf q) (961)) (countLit q [-78, -80]) (countLit q [-84, -85]) (count961 q) 1 (meaning957 q) (meaning961 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 961 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 959 = false ∨ valuationOf q 962 = true := by
  have hs : count961 q = (countLit q [-78, -80]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-84, -85])
  have hm := merge_two (literal (valuationOf q) (957)) (literal (valuationOf q) (959)) (literal (valuationOf q) (962)) (countLit q [-78, -80]) (countLit q [-84, -85]) (count961 q) 1 1 (meaning957 q) (meaning959 q) (meaning962 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 959 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 959 = false ∨ valuation q 962 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 960 = false ∨ valuationOf q 963 = true := by
  have hs : count961 q = (countLit q [-78, -80]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-84, -85])
  have hm := merge_two (literal (valuationOf q) (957)) (literal (valuationOf q) (960)) (literal (valuationOf q) (963)) (countLit q [-78, -80]) (countLit q [-84, -85]) (count961 q) 1 2 (meaning957 q) (meaning960 q) (meaning963 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 960 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 960 = false ∨ valuation q 963 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 962 = true := by
  have hs : count961 q = (countLit q [-78, -80]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-84, -85])
  have hm := merge_left (literal (valuationOf q) (958)) (literal (valuationOf q) (962)) (countLit q [-78, -80]) (countLit q [-84, -85]) (count961 q) 2 (meaning958 q) (meaning962 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 962 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 959 = false ∨ valuationOf q 963 = true := by
  have hs : count961 q = (countLit q [-78, -80]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-84, -85])
  have hm := merge_two (literal (valuationOf q) (958)) (literal (valuationOf q) (959)) (literal (valuationOf q) (963)) (countLit q [-78, -80]) (countLit q [-84, -85]) (count961 q) 2 1 (meaning958 q) (meaning959 q) (meaning963 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 959 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 959 = false ∨ valuation q 963 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 965 = true := by
  have hs : count965 q = (countLit q [-70, -73, -76, -77]) + (countLit q [-78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-70, -73, -76, -77]) (l₂ := [-78, -80, -84, -85])
  have hm := merge_right (literal (valuationOf q) (961)) (literal (valuationOf q) (965)) (countLit q [-70, -73, -76, -77]) (countLit q [-78, -80, -84, -85]) (count965 q) 1 (meaning961 q) (meaning965 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 965 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 966 = true := by
  have hs : count965 q = (countLit q [-70, -73, -76, -77]) + (countLit q [-78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-70, -73, -76, -77]) (l₂ := [-78, -80, -84, -85])
  have hm := merge_right (literal (valuationOf q) (962)) (literal (valuationOf q) (966)) (countLit q [-70, -73, -76, -77]) (countLit q [-78, -80, -84, -85]) (count965 q) 2 (meaning962 q) (meaning966 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 966 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 967 = true := by
  have hs : count965 q = (countLit q [-70, -73, -76, -77]) + (countLit q [-78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-70, -73, -76, -77]) (l₂ := [-78, -80, -84, -85])
  have hm := merge_right (literal (valuationOf q) (963)) (literal (valuationOf q) (967)) (countLit q [-70, -73, -76, -77]) (countLit q [-78, -80, -84, -85]) (count965 q) 3 (meaning963 q) (meaning967 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 967 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 961 = false ∨ valuationOf q 966 = true := by
  have hs : count965 q = (countLit q [-70, -73, -76, -77]) + (countLit q [-78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-70, -73, -76, -77]) (l₂ := [-78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (953)) (literal (valuationOf q) (961)) (literal (valuationOf q) (966)) (countLit q [-70, -73, -76, -77]) (countLit q [-78, -80, -84, -85]) (count965 q) 1 1 (meaning953 q) (meaning961 q) (meaning966 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 961 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 961 = false ∨ valuation q 966 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 962 = false ∨ valuationOf q 967 = true := by
  have hs : count965 q = (countLit q [-70, -73, -76, -77]) + (countLit q [-78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-70, -73, -76, -77]) (l₂ := [-78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (953)) (literal (valuationOf q) (962)) (literal (valuationOf q) (967)) (countLit q [-70, -73, -76, -77]) (countLit q [-78, -80, -84, -85]) (count965 q) 1 2 (meaning953 q) (meaning962 q) (meaning967 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 962 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 962 = false ∨ valuation q 967 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 966 = true := by
  have hs : count965 q = (countLit q [-70, -73, -76, -77]) + (countLit q [-78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-70, -73, -76, -77]) (l₂ := [-78, -80, -84, -85])
  have hm := merge_left (literal (valuationOf q) (954)) (literal (valuationOf q) (966)) (countLit q [-70, -73, -76, -77]) (countLit q [-78, -80, -84, -85]) (count965 q) 2 (meaning954 q) (meaning966 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 966 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 961 = false ∨ valuationOf q 967 = true := by
  have hs : count965 q = (countLit q [-70, -73, -76, -77]) + (countLit q [-78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-70, -73, -76, -77]) (l₂ := [-78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (954)) (literal (valuationOf q) (961)) (literal (valuationOf q) (967)) (countLit q [-70, -73, -76, -77]) (countLit q [-78, -80, -84, -85]) (count965 q) 2 1 (meaning954 q) (meaning961 q) (meaning967 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 961 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 961 = false ∨ valuation q 967 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 962 = false ∨ valuationOf q 968 = true := by
  have hs : count965 q = (countLit q [-70, -73, -76, -77]) + (countLit q [-78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-70, -73, -76, -77]) (l₂ := [-78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (954)) (literal (valuationOf q) (962)) (literal (valuationOf q) (968)) (countLit q [-70, -73, -76, -77]) (countLit q [-78, -80, -84, -85]) (count965 q) 2 2 (meaning954 q) (meaning962 q) (meaning968 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 962 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 962 = false ∨ valuation q 968 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 961 = false ∨ valuationOf q 968 = true := by
  have hs : count965 q = (countLit q [-70, -73, -76, -77]) + (countLit q [-78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-70, -73, -76, -77]) (l₂ := [-78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (955)) (literal (valuationOf q) (961)) (literal (valuationOf q) (968)) (countLit q [-70, -73, -76, -77]) (countLit q [-78, -80, -84, -85]) (count965 q) 3 1 (meaning955 q) (meaning961 q) (meaning968 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 961 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 961 = false ∨ valuation q 968 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 956 = false ∨ valuationOf q 961 = false ∨ valuationOf q 969 = true := by
  have hs : count965 q = (countLit q [-70, -73, -76, -77]) + (countLit q [-78, -80, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-70, -73, -76, -77]) (l₂ := [-78, -80, -84, -85])
  have hm := merge_two (literal (valuationOf q) (956)) (literal (valuationOf q) (961)) (literal (valuationOf q) (969)) (countLit q [-70, -73, -76, -77]) (countLit q [-78, -80, -84, -85]) (count965 q) 4 1 (meaning956 q) (meaning961 q) (meaning969 q) hs
  change valuationOf q 956 = false ∨ valuationOf q 961 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 956 = false ∨ valuation q 961 = false ∨ valuation q 969 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E203.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112203
