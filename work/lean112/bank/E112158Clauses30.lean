import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 75 = true ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-72]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-75])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-75)) (literal (valuationOf q) (954)) (countLit q [-72]) (countLit q [-75]) (count953 q) 1 1 (meaningNeg72 q) (meaningNeg75 q) (meaning954 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 75)) = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 75 = true ∨ valuation q 954 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 955 = true := by
  have hs : count955 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (955)) (countLit q [-76]) (countLit q [-79]) (count955 q) 1 (meaningNeg76 q) (meaning955 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 955 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 957 = true := by
  have hs : count957 q = (countLit q [-72, -75]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-76, -79])
  have hm := merge_left (literal (valuationOf q) (953)) (literal (valuationOf q) (957)) (countLit q [-72, -75]) (countLit q [-76, -79]) (count957 q) 1 (meaning953 q) (meaning957 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 957 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 955 = false ∨ valuationOf q 959 = true := by
  have hs : count957 q = (countLit q [-72, -75]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -75]) (l₂ := [-76, -79])
  have hm := merge_two (literal (valuationOf q) (954)) (literal (valuationOf q) (955)) (literal (valuationOf q) (959)) (countLit q [-72, -75]) (countLit q [-76, -79]) (count957 q) 2 1 (meaning954 q) (meaning955 q) (meaning959 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 955 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 955 = false ∨ valuation q 959 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 961 = true := by
  have hs : count961 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_right (literal (valuationOf q) (-83)) (literal (valuationOf q) (961)) (countLit q [-81]) (countLit q [-83]) (count961 q) 1 (meaningNeg83 q) (meaning961 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 961 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 965 = true := by
  have hs : count965 q = (countLit q [-81, -83]) + (countLit q [-85, -88]) := List.countP_append (p := literal q) (l₁ := [-81, -83]) (l₂ := [-85, -88])
  have hm := merge_left (literal (valuationOf q) (961)) (literal (valuationOf q) (965)) (countLit q [-81, -83]) (countLit q [-85, -88]) (count965 q) 1 (meaning961 q) (meaning965 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 965 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 969 = true := by
  have hs : count969 q = (countLit q [-72, -75, -76, -79]) + (countLit q [-81, -83, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-72, -75, -76, -79]) (l₂ := [-81, -83, -85, -88])
  have hm := merge_left (literal (valuationOf q) (957)) (literal (valuationOf q) (969)) (countLit q [-72, -75, -76, -79]) (countLit q [-81, -83, -85, -88]) (count969 q) 1 (meaning957 q) (meaning969 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 969 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 965 = false ∨ valuationOf q 972 = true := by
  have hs : count969 q = (countLit q [-72, -75, -76, -79]) + (countLit q [-81, -83, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-72, -75, -76, -79]) (l₂ := [-81, -83, -85, -88])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (965)) (literal (valuationOf q) (972)) (countLit q [-72, -75, -76, -79]) (countLit q [-81, -83, -85, -88]) (count969 q) 3 1 (meaning959 q) (meaning965 q) (meaning972 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 965 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 965 = false ∨ valuation q 972 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 972 = false ∨ valuationOf q 981 = true := by
  have hs : count977 q = (countLit q [-60, -62, -64, -66, -67, -69, -70]) + (countLit q [-72, -75, -76, -79, -81, -83, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -64, -66, -67, -69, -70]) (l₂ := [-72, -75, -76, -79, -81, -83, -85, -88])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (972)) (literal (valuationOf q) (981)) (countLit q [-60, -62, -64, -66, -67, -69, -70]) (countLit q [-72, -75, -76, -79, -81, -83, -85, -88]) (count977 q) 1 4 (meaning946 q) (meaning972 q) (meaning981 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 972 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 972 = false ∨ valuation q 981 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 969 = false ∨ valuationOf q 980 = true := by
  have hs : count977 q = (countLit q [-60, -62, -64, -66, -67, -69, -70]) + (countLit q [-72, -75, -76, -79, -81, -83, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -64, -66, -67, -69, -70]) (l₂ := [-72, -75, -76, -79, -81, -83, -85, -88])
  have hm := merge_two (literal (valuationOf q) (948)) (literal (valuationOf q) (969)) (literal (valuationOf q) (980)) (countLit q [-60, -62, -64, -66, -67, -69, -70]) (countLit q [-72, -75, -76, -79, -81, -83, -85, -88]) (count977 q) 3 1 (meaning948 q) (meaning969 q) (meaning980 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 969 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 969 = false ∨ valuation q 980 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 994 = true := by
  have hs : count994 q = (countLit q [-90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91, -94])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (994)) (countLit q [-90]) (countLit q [-91, -94]) (count994 q) 1 (meaningNeg90 q) (meaning994 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 994 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 994 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 999 = true := by
  have hs : count999 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (999)) (countLit q [-99]) (countLit q [-101]) (count999 q) 1 (meaningNeg101 q) (meaning999 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 999 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 999 = false ∨ valuationOf q 1001 = true := by
  have hs : count1001 q = (countLit q [-96, -97]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-99, -101])
  have hm := merge_right (literal (valuationOf q) (999)) (literal (valuationOf q) (1001)) (countLit q [-96, -97]) (countLit q [-99, -101]) (count1001 q) 1 (meaning999 q) (meaning1001 q) hs
  change valuationOf q 999 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 999 = false ∨ valuation q 1001 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1005 = true := by
  have hs : count1005 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -97, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -97, -99, -101])
  have hm := merge_right (literal (valuationOf q) (1001)) (literal (valuationOf q) (1005)) (countLit q [-90, -91, -94]) (countLit q [-96, -97, -99, -101]) (count1005 q) 1 (meaning1001 q) (meaning1005 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1005 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 1005 = true := by
  have hs : count1005 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -97, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -97, -99, -101])
  have hm := merge_left (literal (valuationOf q) (994)) (literal (valuationOf q) (1005)) (countLit q [-90, -91, -94]) (countLit q [-96, -97, -99, -101]) (count1005 q) 1 (meaning994 q) (meaning1005 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 1005 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 1001 = false ∨ valuationOf q 1006 = true := by
  have hs : count1005 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -97, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -97, -99, -101])
  have hm := merge_two (literal (valuationOf q) (994)) (literal (valuationOf q) (1001)) (literal (valuationOf q) (1006)) (countLit q [-90, -91, -94]) (countLit q [-96, -97, -99, -101]) (count1005 q) 1 1 (meaning994 q) (meaning1001 q) (meaning1006 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 1001 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 1001 = false ∨ valuation q 1006 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1012 = true := by
  have hs : count1012 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1012)) (countLit q [-103]) (countLit q [-105]) (count1012 q) 1 (meaningNeg103 q) (meaning1012 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1012 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1013)) (countLit q [-103]) (countLit q [-105]) (count1012 q) 1 1 (meaningNeg103 q) (meaningNeg105 q) (meaning1013 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 1013 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1014 = true := by
  have hs : count1014 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1014)) (countLit q [-106]) (countLit q [-108]) (count1014 q) 1 (meaningNeg108 q) (meaning1014 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1014 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1014 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-103, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-106, -108])
  have hm := merge_left (literal (valuationOf q) (1012)) (literal (valuationOf q) (1016)) (countLit q [-103, -105]) (countLit q [-106, -108]) (count1016 q) 1 (meaning1012 q) (meaning1016 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1016 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1014 = false ∨ valuationOf q 1018 = true := by
  have hs : count1016 q = (countLit q [-103, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1014)) (literal (valuationOf q) (1018)) (countLit q [-103, -105]) (countLit q [-106, -108]) (count1016 q) 2 1 (meaning1013 q) (meaning1014 q) (meaning1018 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1014 = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1014 = false ∨ valuation q 1018 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1028 = true := by
  have hs : count1028 q = (countLit q [-103, -105, -106, -108]) + (countLit q [-112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -105, -106, -108]) (l₂ := [-112, -113, -115, -116])
  have hm := merge_left (literal (valuationOf q) (1016)) (literal (valuationOf q) (1028)) (countLit q [-103, -105, -106, -108]) (countLit q [-112, -113, -115, -116]) (count1028 q) 1 (meaning1016 q) (meaning1028 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1028 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1030 = true := by
  have hs : count1028 q = (countLit q [-103, -105, -106, -108]) + (countLit q [-112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -105, -106, -108]) (l₂ := [-112, -113, -115, -116])
  have hm := merge_left (literal (valuationOf q) (1018)) (literal (valuationOf q) (1030)) (countLit q [-103, -105, -106, -108]) (countLit q [-112, -113, -115, -116]) (count1028 q) 3 (meaning1018 q) (meaning1030 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1030 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1030 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1028 = false ∨ valuationOf q 1036 = true := by
  have hs : count1036 q = (countLit q [-90, -91, -94, -96, -97, -99, -101]) + (countLit q [-103, -105, -106, -108, -112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -97, -99, -101]) (l₂ := [-103, -105, -106, -108, -112, -113, -115, -116])
  have hm := merge_right (literal (valuationOf q) (1028)) (literal (valuationOf q) (1036)) (countLit q [-90, -91, -94, -96, -97, -99, -101]) (countLit q [-103, -105, -106, -108, -112, -113, -115, -116]) (count1036 q) 1 (meaning1028 q) (meaning1036 q) hs
  change valuationOf q 1028 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1028 = false ∨ valuation q 1036 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1037 = true := by
  have hs : count1036 q = (countLit q [-90, -91, -94, -96, -97, -99, -101]) + (countLit q [-103, -105, -106, -108, -112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -97, -99, -101]) (l₂ := [-103, -105, -106, -108, -112, -113, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1037)) (countLit q [-90, -91, -94, -96, -97, -99, -101]) (countLit q [-103, -105, -106, -108, -112, -113, -115, -116]) (count1036 q) 1 1 (meaning1005 q) (meaning1028 q) (meaning1037 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1028 = false ∨ valuation q 1037 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1039 = true := by
  have hs : count1036 q = (countLit q [-90, -91, -94, -96, -97, -99, -101]) + (countLit q [-103, -105, -106, -108, -112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -97, -99, -101]) (l₂ := [-103, -105, -106, -108, -112, -113, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1030)) (literal (valuationOf q) (1039)) (countLit q [-90, -91, -94, -96, -97, -99, -101]) (countLit q [-103, -105, -106, -108, -112, -113, -115, -116]) (count1036 q) 1 3 (meaning1005 q) (meaning1030 q) (meaning1039 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1030 = false ∨ valuation q 1039 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1040 = true := by
  have hs : count1036 q = (countLit q [-90, -91, -94, -96, -97, -99, -101]) + (countLit q [-103, -105, -106, -108, -112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -97, -99, -101]) (l₂ := [-103, -105, -106, -108, -112, -113, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1030)) (literal (valuationOf q) (1040)) (countLit q [-90, -91, -94, -96, -97, -99, -101]) (countLit q [-103, -105, -106, -108, -112, -113, -115, -116]) (count1036 q) 2 3 (meaning1006 q) (meaning1030 q) (meaning1040 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1030 = false ∨ valuation q 1040 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1058 = true := by
  have hs : count1051 q = (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88]) + (countLit q [-90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88]) (l₂ := [-90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1039)) (literal (valuationOf q) (1058)) (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88]) (countLit q [-90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) (count1051 q) 4 4 (meaning980 q) (meaning1039 q) (meaning1058 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1039 = false ∨ valuation q 1058 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1059 = true := by
  have hs : count1051 q = (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88]) + (countLit q [-90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88]) (l₂ := [-90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1040)) (literal (valuationOf q) (1059)) (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88]) (countLit q [-90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) (count1051 q) 4 5 (meaning980 q) (meaning1040 q) (meaning1059 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1040 = false ∨ valuation q 1059 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1056 = true := by
  have hs : count1051 q = (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88]) + (countLit q [-90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88]) (l₂ := [-90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116])
  have hm := merge_two (literal (valuationOf q) (981)) (literal (valuationOf q) (1036)) (literal (valuationOf q) (1056)) (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88]) (countLit q [-90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) (count1051 q) 5 1 (meaning981 q) (meaning1036 q) (meaning1056 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 1036 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 1036 = false ∨ valuation q 1056 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1057 = true := by
  have hs : count1051 q = (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88]) + (countLit q [-90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88]) (l₂ := [-90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116])
  have hm := merge_two (literal (valuationOf q) (981)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1057)) (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88]) (countLit q [-90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) (count1051 q) 5 2 (meaning981 q) (meaning1037 q) (meaning1057 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 1037 = false ∨ valuation q 1057 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1088 = true := by
  have hs : count1070 q = (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26, -27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) + (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88, -90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26, -27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) (l₂ := [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88, -90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1088)) (countLit q [-1, -2, -4, -5, -8, -10, -12, -14, -15, -16, -18, -22, -23, -26, -27, -29, -31, -33, -36, -37, -38, -40, -43, -46, -47, -49, -52, -56, -57]) (countLit q [-60, -62, -64, -66, -67, -69, -70, -72, -75, -76, -79, -81, -83, -85, -88, -90, -91, -94, -96, -97, -99, -101, -103, -105, -106, -108, -112, -113, -115, -116]) (count1070 q) 10 9 (meaning923 q) (meaning1059 q) (meaning1088 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 1059 = false ∨ valuation q 1088 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E158.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112158
