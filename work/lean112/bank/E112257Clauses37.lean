import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 955 = false ∨ valuationOf q 963 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (955)) (literal (valuationOf q) (963)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 1 5 (meaning931 q) (meaning955 q) (meaning963 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 955 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 955 = false ∨ valuation q 963 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 959 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_left (literal (valuationOf q) (932)) (literal (valuationOf q) (959)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 2 (meaning932 q) (meaning959 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 959 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 951 = false ∨ valuationOf q 960 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (951)) (literal (valuationOf q) (960)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 2 1 (meaning932 q) (meaning951 q) (meaning960 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 951 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 951 = false ∨ valuation q 960 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 952 = false ∨ valuationOf q 961 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (952)) (literal (valuationOf q) (961)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 2 2 (meaning932 q) (meaning952 q) (meaning961 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 952 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 952 = false ∨ valuation q 961 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 953 = false ∨ valuationOf q 962 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (953)) (literal (valuationOf q) (962)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 2 3 (meaning932 q) (meaning953 q) (meaning962 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 953 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 953 = false ∨ valuation q 962 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 954 = false ∨ valuationOf q 963 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (954)) (literal (valuationOf q) (963)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 2 4 (meaning932 q) (meaning954 q) (meaning963 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 954 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 954 = false ∨ valuation q 963 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 960 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_left (literal (valuationOf q) (933)) (literal (valuationOf q) (960)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 3 (meaning933 q) (meaning960 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 960 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 951 = false ∨ valuationOf q 961 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (951)) (literal (valuationOf q) (961)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 3 1 (meaning933 q) (meaning951 q) (meaning961 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 951 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 951 = false ∨ valuation q 961 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 952 = false ∨ valuationOf q 962 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (952)) (literal (valuationOf q) (962)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 3 2 (meaning933 q) (meaning952 q) (meaning962 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 952 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 952 = false ∨ valuation q 962 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 953 = false ∨ valuationOf q 963 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (953)) (literal (valuationOf q) (963)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 3 3 (meaning933 q) (meaning953 q) (meaning963 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 953 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 953 = false ∨ valuation q 963 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 961 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_left (literal (valuationOf q) (934)) (literal (valuationOf q) (961)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 4 (meaning934 q) (meaning961 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 961 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 951 = false ∨ valuationOf q 962 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (951)) (literal (valuationOf q) (962)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 4 1 (meaning934 q) (meaning951 q) (meaning962 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 951 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 951 = false ∨ valuation q 962 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 952 = false ∨ valuationOf q 963 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (952)) (literal (valuationOf q) (963)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 4 2 (meaning934 q) (meaning952 q) (meaning963 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 952 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 952 = false ∨ valuation q 963 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 962 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_left (literal (valuationOf q) (935)) (literal (valuationOf q) (962)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 5 (meaning935 q) (meaning962 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 962 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 951 = false ∨ valuationOf q 963 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (951)) (literal (valuationOf q) (963)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 5 1 (meaning935 q) (meaning951 q) (meaning963 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 951 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 951 = false ∨ valuation q 963 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 952 = false ∨ valuationOf q 964 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -70, -71]) + (countLit q [-72, -75, -79, -81, -82, -85, -87]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71]) (l₂ := [-72, -75, -79, -81, -82, -85, -87])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (952)) (literal (valuationOf q) (964)) (countLit q [-62, -63, -64, -66, -68, -70, -71]) (countLit q [-72, -75, -79, -81, -82, -85, -87]) (count958 q) 5 2 (meaning935 q) (meaning952 q) (meaning964 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 952 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 952 = false ∨ valuation q 964 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 972 = true := by
  have hs : count972 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (972)) (countLit q [-91]) (countLit q [-93]) (count972 q) 1 (meaningNeg93 q) (meaning972 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 972 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 972 = true := by
  have hs : count972 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (972)) (countLit q [-91]) (countLit q [-93]) (count972 q) 1 (meaningNeg91 q) (meaning972 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 972 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 93 = true ∨ valuationOf q 973 = true := by
  have hs : count972 q = (countLit q [-91]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (973)) (countLit q [-91]) (countLit q [-93]) (count972 q) 1 1 (meaningNeg91 q) (meaningNeg93 q) (meaning973 q) hs
  change (! (valuationOf q 91)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 93 = true ∨ valuation q 973 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 972 = false ∨ valuationOf q 974 = true := by
  have hs : count974 q = (countLit q [-89]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91, -93])
  have hm := merge_right (literal (valuationOf q) (972)) (literal (valuationOf q) (974)) (countLit q [-89]) (countLit q [-91, -93]) (count974 q) 1 (meaning972 q) (meaning974 q) hs
  change valuationOf q 972 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 972 = false ∨ valuation q 974 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 975 = true := by
  have hs : count974 q = (countLit q [-89]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91, -93])
  have hm := merge_right (literal (valuationOf q) (973)) (literal (valuationOf q) (975)) (countLit q [-89]) (countLit q [-91, -93]) (count974 q) 2 (meaning973 q) (meaning975 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 975 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 974 = true := by
  have hs : count974 q = (countLit q [-89]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91, -93])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (974)) (countLit q [-89]) (countLit q [-91, -93]) (count974 q) 1 (meaningNeg89 q) (meaning974 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 974 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 972 = false ∨ valuationOf q 975 = true := by
  have hs : count974 q = (countLit q [-89]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91, -93])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (972)) (literal (valuationOf q) (975)) (countLit q [-89]) (countLit q [-91, -93]) (count974 q) 1 1 (meaningNeg89 q) (meaning972 q) (meaning975 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 972 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 972 = false ∨ valuation q 975 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 973 = false ∨ valuationOf q 976 = true := by
  have hs : count974 q = (countLit q [-89]) + (countLit q [-91, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91, -93])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (973)) (literal (valuationOf q) (976)) (countLit q [-89]) (countLit q [-91, -93]) (count974 q) 1 2 (meaningNeg89 q) (meaning973 q) (meaning976 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 973 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 973 = false ∨ valuation q 976 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 977 = true := by
  have hs : count977 q = (countLit q [-95]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (977)) (countLit q [-95]) (countLit q [-99]) (count977 q) 1 (meaningNeg99 q) (meaning977 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 977 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 979 = true := by
  have hs : count979 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (979)) (countLit q [-101]) (countLit q [-102]) (count979 q) 1 (meaningNeg101 q) (meaning979 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 979 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 102 = true ∨ valuationOf q 980 = true := by
  have hs : count979 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_two (literal (valuationOf q) (-101)) (literal (valuationOf q) (-102)) (literal (valuationOf q) (980)) (countLit q [-101]) (countLit q [-102]) (count979 q) 1 1 (meaningNeg101 q) (meaningNeg102 q) (meaning980 q) hs
  change (! (valuationOf q 101)) = false ∨ (! (valuationOf q 102)) = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 102 = true ∨ valuation q 980 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 981 = true := by
  have hs : count981 q = (countLit q [-95, -99]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -99]) (l₂ := [-101, -102])
  have hm := merge_right (literal (valuationOf q) (979)) (literal (valuationOf q) (981)) (countLit q [-95, -99]) (countLit q [-101, -102]) (count981 q) 1 (meaning979 q) (meaning981 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 981 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 982 = true := by
  have hs : count981 q = (countLit q [-95, -99]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -99]) (l₂ := [-101, -102])
  have hm := merge_right (literal (valuationOf q) (980)) (literal (valuationOf q) (982)) (countLit q [-95, -99]) (countLit q [-101, -102]) (count981 q) 2 (meaning980 q) (meaning982 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 982 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 981 = true := by
  have hs : count981 q = (countLit q [-95, -99]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -99]) (l₂ := [-101, -102])
  have hm := merge_left (literal (valuationOf q) (977)) (literal (valuationOf q) (981)) (countLit q [-95, -99]) (countLit q [-101, -102]) (count981 q) 1 (meaning977 q) (meaning981 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 981 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 979 = false ∨ valuationOf q 982 = true := by
  have hs : count981 q = (countLit q [-95, -99]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -99]) (l₂ := [-101, -102])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (979)) (literal (valuationOf q) (982)) (countLit q [-95, -99]) (countLit q [-101, -102]) (count981 q) 1 1 (meaning977 q) (meaning979 q) (meaning982 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 979 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 979 = false ∨ valuation q 982 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 985 = true := by
  have hs : count985 q = (countLit q [-89, -91, -93]) + (countLit q [-95, -99, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -93]) (l₂ := [-95, -99, -101, -102])
  have hm := merge_right (literal (valuationOf q) (981)) (literal (valuationOf q) (985)) (countLit q [-89, -91, -93]) (countLit q [-95, -99, -101, -102]) (count985 q) 1 (meaning981 q) (meaning985 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 985 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E257.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112257
