import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 950 = false ∨ valuationOf q 957 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (950)) (literal (valuationOf q) (957)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 3 4 (meaning942 q) (meaning950 q) (meaning957 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 950 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 950 = false ∨ valuation q 957 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 959 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_right (literal (valuationOf q) (952)) (literal (valuationOf q) (959)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 2 (meaning952 q) (meaning959 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 959 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 960 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_right (literal (valuationOf q) (953)) (literal (valuationOf q) (960)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 3 (meaning953 q) (meaning960 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 960 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 951 = false ∨ valuationOf q 959 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (951)) (literal (valuationOf q) (959)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 1 1 (meaning931 q) (meaning951 q) (meaning959 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 951 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 951 = false ∨ valuation q 959 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 952 = false ∨ valuationOf q 960 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (952)) (literal (valuationOf q) (960)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 1 2 (meaning931 q) (meaning952 q) (meaning960 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 952 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 952 = false ∨ valuation q 960 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 953 = false ∨ valuationOf q 961 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (953)) (literal (valuationOf q) (961)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 1 3 (meaning931 q) (meaning953 q) (meaning961 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 953 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 953 = false ∨ valuation q 961 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 954 = false ∨ valuationOf q 962 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (954)) (literal (valuationOf q) (962)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 1 4 (meaning931 q) (meaning954 q) (meaning962 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 954 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 954 = false ∨ valuation q 962 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 955 = false ∨ valuationOf q 963 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (955)) (literal (valuationOf q) (963)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 1 5 (meaning931 q) (meaning955 q) (meaning963 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 955 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 955 = false ∨ valuation q 963 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 956 = false ∨ valuationOf q 964 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (956)) (literal (valuationOf q) (964)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 1 6 (meaning931 q) (meaning956 q) (meaning964 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 956 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 956 = false ∨ valuation q 964 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 951 = false ∨ valuationOf q 960 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (951)) (literal (valuationOf q) (960)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 2 1 (meaning932 q) (meaning951 q) (meaning960 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 951 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 951 = false ∨ valuation q 960 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 952 = false ∨ valuationOf q 961 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (952)) (literal (valuationOf q) (961)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 2 2 (meaning932 q) (meaning952 q) (meaning961 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 952 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 952 = false ∨ valuation q 961 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 953 = false ∨ valuationOf q 962 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (953)) (literal (valuationOf q) (962)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 2 3 (meaning932 q) (meaning953 q) (meaning962 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 953 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 953 = false ∨ valuation q 962 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 954 = false ∨ valuationOf q 963 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (954)) (literal (valuationOf q) (963)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 2 4 (meaning932 q) (meaning954 q) (meaning963 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 954 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 954 = false ∨ valuation q 963 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 955 = false ∨ valuationOf q 964 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (955)) (literal (valuationOf q) (964)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 2 5 (meaning932 q) (meaning955 q) (meaning964 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 955 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 955 = false ∨ valuation q 964 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 956 = false ∨ valuationOf q 965 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (956)) (literal (valuationOf q) (965)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 2 6 (meaning932 q) (meaning956 q) (meaning965 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 956 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 956 = false ∨ valuation q 965 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 957 = false ∨ valuationOf q 966 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (957)) (literal (valuationOf q) (966)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 2 7 (meaning932 q) (meaning957 q) (meaning966 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 957 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 957 = false ∨ valuation q 966 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 951 = false ∨ valuationOf q 961 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (951)) (literal (valuationOf q) (961)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 3 1 (meaning933 q) (meaning951 q) (meaning961 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 951 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 951 = false ∨ valuation q 961 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 952 = false ∨ valuationOf q 962 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (952)) (literal (valuationOf q) (962)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 3 2 (meaning933 q) (meaning952 q) (meaning962 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 952 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 952 = false ∨ valuation q 962 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 953 = false ∨ valuationOf q 963 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (953)) (literal (valuationOf q) (963)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 3 3 (meaning933 q) (meaning953 q) (meaning963 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 953 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 953 = false ∨ valuation q 963 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 954 = false ∨ valuationOf q 964 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (954)) (literal (valuationOf q) (964)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 3 4 (meaning933 q) (meaning954 q) (meaning964 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 954 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 954 = false ∨ valuation q 964 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 955 = false ∨ valuationOf q 965 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (955)) (literal (valuationOf q) (965)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 3 5 (meaning933 q) (meaning955 q) (meaning965 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 955 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 955 = false ∨ valuation q 965 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 956 = false ∨ valuationOf q 966 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (956)) (literal (valuationOf q) (966)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 3 6 (meaning933 q) (meaning956 q) (meaning966 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 956 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 956 = false ∨ valuation q 966 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 951 = false ∨ valuationOf q 962 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (951)) (literal (valuationOf q) (962)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 4 1 (meaning934 q) (meaning951 q) (meaning962 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 951 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 951 = false ∨ valuation q 962 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 952 = false ∨ valuationOf q 963 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (952)) (literal (valuationOf q) (963)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 4 2 (meaning934 q) (meaning952 q) (meaning963 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 952 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 952 = false ∨ valuation q 963 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 953 = false ∨ valuationOf q 964 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (953)) (literal (valuationOf q) (964)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 4 3 (meaning934 q) (meaning953 q) (meaning964 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 953 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 953 = false ∨ valuation q 964 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 954 = false ∨ valuationOf q 965 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (954)) (literal (valuationOf q) (965)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 4 4 (meaning934 q) (meaning954 q) (meaning965 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 954 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 954 = false ∨ valuation q 965 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 955 = false ∨ valuationOf q 966 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (955)) (literal (valuationOf q) (966)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 4 5 (meaning934 q) (meaning955 q) (meaning966 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 955 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 955 = false ∨ valuation q 966 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 951 = false ∨ valuationOf q 963 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (951)) (literal (valuationOf q) (963)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 5 1 (meaning935 q) (meaning951 q) (meaning963 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 951 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 951 = false ∨ valuation q 963 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 952 = false ∨ valuationOf q 964 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (952)) (literal (valuationOf q) (964)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 5 2 (meaning935 q) (meaning952 q) (meaning964 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 952 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 952 = false ∨ valuation q 964 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 953 = false ∨ valuationOf q 965 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (953)) (literal (valuationOf q) (965)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 5 3 (meaning935 q) (meaning953 q) (meaning965 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 953 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 953 = false ∨ valuation q 965 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 954 = false ∨ valuationOf q 966 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (954)) (literal (valuationOf q) (966)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 5 4 (meaning935 q) (meaning954 q) (meaning966 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 954 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 954 = false ∨ valuation q 966 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 955 = false ∨ valuationOf q 967 = true := by
  have hs : count958 q = (countLit q [-62, -63, -64, -66, -68, -69, -74]) + (countLit q [-75, -78, -82, -84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -69, -74]) (l₂ := [-75, -78, -82, -84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (955)) (literal (valuationOf q) (967)) (countLit q [-62, -63, -64, -66, -68, -69, -74]) (countLit q [-75, -78, -82, -84, -85, -87, -88]) (count958 q) 5 5 (meaning935 q) (meaning955 q) (meaning967 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 955 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 955 = false ∨ valuation q 967 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E259.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112259
