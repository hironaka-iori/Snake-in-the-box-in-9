import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 962 = true := by
  have hs : count962 q = (countLit q [-85]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86, -90])
  have hm := merge_right (literal (valuationOf q) (960)) (literal (valuationOf q) (962)) (countLit q [-85]) (countLit q [-86, -90]) (count962 q) 1 (meaning960 q) (meaning962 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 962 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 963 = true := by
  have hs : count962 q = (countLit q [-85]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86, -90])
  have hm := merge_right (literal (valuationOf q) (961)) (literal (valuationOf q) (963)) (countLit q [-85]) (countLit q [-86, -90]) (count962 q) 2 (meaning961 q) (meaning963 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 963 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 962 = true := by
  have hs : count962 q = (countLit q [-85]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86, -90])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (962)) (countLit q [-85]) (countLit q [-86, -90]) (count962 q) 1 (meaningNeg85 q) (meaning962 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 962 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 960 = false ∨ valuationOf q 963 = true := by
  have hs : count962 q = (countLit q [-85]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86, -90])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (960)) (literal (valuationOf q) (963)) (countLit q [-85]) (countLit q [-86, -90]) (count962 q) 1 1 (meaningNeg85 q) (meaning960 q) (meaning963 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 960 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 960 = false ∨ valuation q 963 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 961 = false ∨ valuationOf q 964 = true := by
  have hs : count962 q = (countLit q [-85]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86, -90])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (961)) (literal (valuationOf q) (964)) (countLit q [-85]) (countLit q [-86, -90]) (count962 q) 1 2 (meaningNeg85 q) (meaning961 q) (meaning964 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 961 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 961 = false ∨ valuation q 964 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 965 = true := by
  have hs : count965 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (965)) (countLit q [-91]) (countLit q [-93]) (count965 q) 1 (meaningNeg93 q) (meaning965 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 965 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 965 = true := by
  have hs : count965 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (965)) (countLit q [-91]) (countLit q [-93]) (count965 q) 1 (meaningNeg91 q) (meaning965 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 965 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 93 = true ∨ valuationOf q 966 = true := by
  have hs : count965 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (966)) (countLit q [-91]) (countLit q [-93]) (count965 q) 1 1 (meaningNeg91 q) (meaningNeg93 q) (meaning966 q) hs
  change (! (valuationOf q 91)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 93 = true ∨ valuation q 966 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 967 = true := by
  have hs : count967 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (967)) (countLit q [-95]) (countLit q [-97]) (count967 q) 1 (meaningNeg97 q) (meaning967 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 967 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 967 = true := by
  have hs : count967 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (967)) (countLit q [-95]) (countLit q [-97]) (count967 q) 1 (meaningNeg95 q) (meaning967 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 967 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 97 = true ∨ valuationOf q 968 = true := by
  have hs : count967 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (968)) (countLit q [-95]) (countLit q [-97]) (count967 q) 1 1 (meaningNeg95 q) (meaningNeg97 q) (meaning968 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 968 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 967 = false ∨ valuationOf q 969 = true := by
  have hs : count969 q = (countLit q [-91, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuationOf q) (967)) (literal (valuationOf q) (969)) (countLit q [-91, -93]) (countLit q [-95, -97]) (count969 q) 1 (meaning967 q) (meaning969 q) hs
  change valuationOf q 967 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 967 = false ∨ valuation q 969 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 968 = false ∨ valuationOf q 970 = true := by
  have hs : count969 q = (countLit q [-91, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuationOf q) (968)) (literal (valuationOf q) (970)) (countLit q [-91, -93]) (countLit q [-95, -97]) (count969 q) 2 (meaning968 q) (meaning970 q) hs
  change valuationOf q 968 = false ∨ valuationOf q 970 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 968 = false ∨ valuation q 970 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 965 = false ∨ valuationOf q 969 = true := by
  have hs : count969 q = (countLit q [-91, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-95, -97])
  have hm := merge_left (literal (valuationOf q) (965)) (literal (valuationOf q) (969)) (countLit q [-91, -93]) (countLit q [-95, -97]) (count969 q) 1 (meaning965 q) (meaning969 q) hs
  change valuationOf q 965 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 965 = false ∨ valuation q 969 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 965 = false ∨ valuationOf q 967 = false ∨ valuationOf q 970 = true := by
  have hs : count969 q = (countLit q [-91, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuationOf q) (965)) (literal (valuationOf q) (967)) (literal (valuationOf q) (970)) (countLit q [-91, -93]) (countLit q [-95, -97]) (count969 q) 1 1 (meaning965 q) (meaning967 q) (meaning970 q) hs
  change valuationOf q 965 = false ∨ valuationOf q 967 = false ∨ valuationOf q 970 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 965 = false ∨ valuation q 967 = false ∨ valuation q 970 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 965 = false ∨ valuationOf q 968 = false ∨ valuationOf q 971 = true := by
  have hs : count969 q = (countLit q [-91, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuationOf q) (965)) (literal (valuationOf q) (968)) (literal (valuationOf q) (971)) (countLit q [-91, -93]) (countLit q [-95, -97]) (count969 q) 1 2 (meaning965 q) (meaning968 q) (meaning971 q) hs
  change valuationOf q 965 = false ∨ valuationOf q 968 = false ∨ valuationOf q 971 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 965 = false ∨ valuation q 968 = false ∨ valuation q 971 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 966 = false ∨ valuationOf q 970 = true := by
  have hs : count969 q = (countLit q [-91, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-95, -97])
  have hm := merge_left (literal (valuationOf q) (966)) (literal (valuationOf q) (970)) (countLit q [-91, -93]) (countLit q [-95, -97]) (count969 q) 2 (meaning966 q) (meaning970 q) hs
  change valuationOf q 966 = false ∨ valuationOf q 970 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 966 = false ∨ valuation q 970 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 966 = false ∨ valuationOf q 967 = false ∨ valuationOf q 971 = true := by
  have hs : count969 q = (countLit q [-91, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuationOf q) (966)) (literal (valuationOf q) (967)) (literal (valuationOf q) (971)) (countLit q [-91, -93]) (countLit q [-95, -97]) (count969 q) 2 1 (meaning966 q) (meaning967 q) (meaning971 q) hs
  change valuationOf q 966 = false ∨ valuationOf q 967 = false ∨ valuationOf q 971 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 966 = false ∨ valuation q 967 = false ∨ valuation q 971 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 966 = false ∨ valuationOf q 968 = false ∨ valuationOf q 972 = true := by
  have hs : count969 q = (countLit q [-91, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuationOf q) (966)) (literal (valuationOf q) (968)) (literal (valuationOf q) (972)) (countLit q [-91, -93]) (countLit q [-95, -97]) (count969 q) 2 2 (meaning966 q) (meaning968 q) (meaning972 q) hs
  change valuationOf q 966 = false ∨ valuationOf q 968 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 966 = false ∨ valuation q 968 = false ∨ valuation q 972 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 969 = false ∨ valuationOf q 973 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_right (literal (valuationOf q) (969)) (literal (valuationOf q) (973)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 1 (meaning969 q) (meaning973 q) hs
  change valuationOf q 969 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 969 = false ∨ valuation q 973 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 970 = false ∨ valuationOf q 974 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_right (literal (valuationOf q) (970)) (literal (valuationOf q) (974)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 2 (meaning970 q) (meaning974 q) hs
  change valuationOf q 970 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 970 = false ∨ valuation q 974 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 971 = false ∨ valuationOf q 975 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_right (literal (valuationOf q) (971)) (literal (valuationOf q) (975)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 3 (meaning971 q) (meaning975 q) hs
  change valuationOf q 971 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 971 = false ∨ valuation q 975 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 972 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_right (literal (valuationOf q) (972)) (literal (valuationOf q) (976)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 4 (meaning972 q) (meaning976 q) hs
  change valuationOf q 972 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 972 = false ∨ valuation q 976 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 973 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_left (literal (valuationOf q) (962)) (literal (valuationOf q) (973)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 1 (meaning962 q) (meaning973 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 973 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 969 = false ∨ valuationOf q 974 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (962)) (literal (valuationOf q) (969)) (literal (valuationOf q) (974)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 1 1 (meaning962 q) (meaning969 q) (meaning974 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 969 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 969 = false ∨ valuation q 974 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 970 = false ∨ valuationOf q 975 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (962)) (literal (valuationOf q) (970)) (literal (valuationOf q) (975)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 1 2 (meaning962 q) (meaning970 q) (meaning975 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 970 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 970 = false ∨ valuation q 975 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 971 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (962)) (literal (valuationOf q) (971)) (literal (valuationOf q) (976)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 1 3 (meaning962 q) (meaning971 q) (meaning976 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 971 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 971 = false ∨ valuation q 976 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 974 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_left (literal (valuationOf q) (963)) (literal (valuationOf q) (974)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 2 (meaning963 q) (meaning974 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 974 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 969 = false ∨ valuationOf q 975 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (963)) (literal (valuationOf q) (969)) (literal (valuationOf q) (975)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 2 1 (meaning963 q) (meaning969 q) (meaning975 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 969 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 969 = false ∨ valuation q 975 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 970 = false ∨ valuationOf q 976 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (963)) (literal (valuationOf q) (970)) (literal (valuationOf q) (976)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 2 2 (meaning963 q) (meaning970 q) (meaning976 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 970 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 970 = false ∨ valuation q 976 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 971 = false ∨ valuationOf q 977 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_two (literal (valuationOf q) (963)) (literal (valuationOf q) (971)) (literal (valuationOf q) (977)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 2 3 (meaning963 q) (meaning971 q) (meaning977 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 971 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 971 = false ∨ valuation q 977 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 964 = false ∨ valuationOf q 975 = true := by
  have hs : count973 q = (countLit q [-85, -86, -90]) + (countLit q [-91, -93, -95, -97]) := List.countP_append (p := literal q) (l₁ := [-85, -86, -90]) (l₂ := [-91, -93, -95, -97])
  have hm := merge_left (literal (valuationOf q) (964)) (literal (valuationOf q) (975)) (countLit q [-85, -86, -90]) (countLit q [-91, -93, -95, -97]) (count973 q) 3 (meaning964 q) (meaning975 q) hs
  change valuationOf q 964 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 964 = false ∨ valuation q 975 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E051.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112051
