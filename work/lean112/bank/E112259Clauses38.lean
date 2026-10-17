import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 972 = true := by
  have hs : count972 q = (countLit q [-91]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (972)) (countLit q [-91]) (countLit q [-94]) (count972 q) 1 (meaningNeg94 q) (meaning972 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 972 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 972 = true := by
  have hs : count972 q = (countLit q [-91]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (972)) (countLit q [-91]) (countLit q [-94]) (count972 q) 1 (meaningNeg91 q) (meaning972 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 972 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 94 = true ∨ valuationOf q 973 = true := by
  have hs : count972 q = (countLit q [-91]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (973)) (countLit q [-91]) (countLit q [-94]) (count972 q) 1 1 (meaningNeg91 q) (meaningNeg94 q) (meaning973 q) hs
  change (! (valuationOf q 91)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 94 = true ∨ valuation q 973 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 972 = false ∨ valuationOf q 974 = true := by
  have hs : count974 q = (countLit q [-89]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91, -94])
  have hm := merge_right (literal (valuationOf q) (972)) (literal (valuationOf q) (974)) (countLit q [-89]) (countLit q [-91, -94]) (count974 q) 1 (meaning972 q) (meaning974 q) hs
  change valuationOf q 972 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 972 = false ∨ valuation q 974 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 975 = true := by
  have hs : count974 q = (countLit q [-89]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91, -94])
  have hm := merge_right (literal (valuationOf q) (973)) (literal (valuationOf q) (975)) (countLit q [-89]) (countLit q [-91, -94]) (count974 q) 2 (meaning973 q) (meaning975 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 975 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 974 = true := by
  have hs : count974 q = (countLit q [-89]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91, -94])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (974)) (countLit q [-89]) (countLit q [-91, -94]) (count974 q) 1 (meaningNeg89 q) (meaning974 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 974 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 972 = false ∨ valuationOf q 975 = true := by
  have hs : count974 q = (countLit q [-89]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91, -94])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (972)) (literal (valuationOf q) (975)) (countLit q [-89]) (countLit q [-91, -94]) (count974 q) 1 1 (meaningNeg89 q) (meaning972 q) (meaning975 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 972 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 972 = false ∨ valuation q 975 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 973 = false ∨ valuationOf q 976 = true := by
  have hs : count974 q = (countLit q [-89]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91, -94])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (973)) (literal (valuationOf q) (976)) (countLit q [-89]) (countLit q [-91, -94]) (count974 q) 1 2 (meaningNeg89 q) (meaning973 q) (meaning976 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 973 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 973 = false ∨ valuation q 976 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 977 = true := by
  have hs : count977 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (977)) (countLit q [-95]) (countLit q [-97]) (count977 q) 1 (meaningNeg97 q) (meaning977 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 977 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 977 = true := by
  have hs : count977 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (977)) (countLit q [-95]) (countLit q [-97]) (count977 q) 1 (meaningNeg95 q) (meaning977 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 977 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 979 = true := by
  have hs : count979 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (979)) (countLit q [-99]) (countLit q [-101]) (count979 q) 1 (meaningNeg101 q) (meaning979 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 979 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 979 = true := by
  have hs : count979 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (979)) (countLit q [-99]) (countLit q [-101]) (count979 q) 1 (meaningNeg99 q) (meaning979 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 979 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 981 = true := by
  have hs : count981 q = (countLit q [-95, -97]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-99, -101])
  have hm := merge_right (literal (valuationOf q) (979)) (literal (valuationOf q) (981)) (countLit q [-95, -97]) (countLit q [-99, -101]) (count981 q) 1 (meaning979 q) (meaning981 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 981 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 981 = true := by
  have hs : count981 q = (countLit q [-95, -97]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-99, -101])
  have hm := merge_left (literal (valuationOf q) (977)) (literal (valuationOf q) (981)) (countLit q [-95, -97]) (countLit q [-99, -101]) (count981 q) 1 (meaning977 q) (meaning981 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 981 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 979 = false ∨ valuationOf q 982 = true := by
  have hs : count981 q = (countLit q [-95, -97]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (979)) (literal (valuationOf q) (982)) (countLit q [-95, -97]) (countLit q [-99, -101]) (count981 q) 1 1 (meaning977 q) (meaning979 q) (meaning982 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 979 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 979 = false ∨ valuation q 982 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 985 = true := by
  have hs : count985 q = (countLit q [-89, -91, -94]) + (countLit q [-95, -97, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94]) (l₂ := [-95, -97, -99, -101])
  have hm := merge_right (literal (valuationOf q) (981)) (literal (valuationOf q) (985)) (countLit q [-89, -91, -94]) (countLit q [-95, -97, -99, -101]) (count985 q) 1 (meaning981 q) (meaning985 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 985 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 982 = false ∨ valuationOf q 986 = true := by
  have hs : count985 q = (countLit q [-89, -91, -94]) + (countLit q [-95, -97, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94]) (l₂ := [-95, -97, -99, -101])
  have hm := merge_right (literal (valuationOf q) (982)) (literal (valuationOf q) (986)) (countLit q [-89, -91, -94]) (countLit q [-95, -97, -99, -101]) (count985 q) 2 (meaning982 q) (meaning986 q) hs
  change valuationOf q 982 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 982 = false ∨ valuation q 986 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 985 = true := by
  have hs : count985 q = (countLit q [-89, -91, -94]) + (countLit q [-95, -97, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94]) (l₂ := [-95, -97, -99, -101])
  have hm := merge_left (literal (valuationOf q) (974)) (literal (valuationOf q) (985)) (countLit q [-89, -91, -94]) (countLit q [-95, -97, -99, -101]) (count985 q) 1 (meaning974 q) (meaning985 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 985 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 981 = false ∨ valuationOf q 986 = true := by
  have hs : count985 q = (countLit q [-89, -91, -94]) + (countLit q [-95, -97, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94]) (l₂ := [-95, -97, -99, -101])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (981)) (literal (valuationOf q) (986)) (countLit q [-89, -91, -94]) (countLit q [-95, -97, -99, -101]) (count985 q) 1 1 (meaning974 q) (meaning981 q) (meaning986 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 981 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 981 = false ∨ valuation q 986 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 982 = false ∨ valuationOf q 987 = true := by
  have hs : count985 q = (countLit q [-89, -91, -94]) + (countLit q [-95, -97, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94]) (l₂ := [-95, -97, -99, -101])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (982)) (literal (valuationOf q) (987)) (countLit q [-89, -91, -94]) (countLit q [-95, -97, -99, -101]) (count985 q) 1 2 (meaning974 q) (meaning982 q) (meaning987 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 982 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 982 = false ∨ valuation q 987 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 986 = true := by
  have hs : count985 q = (countLit q [-89, -91, -94]) + (countLit q [-95, -97, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94]) (l₂ := [-95, -97, -99, -101])
  have hm := merge_left (literal (valuationOf q) (975)) (literal (valuationOf q) (986)) (countLit q [-89, -91, -94]) (countLit q [-95, -97, -99, -101]) (count985 q) 2 (meaning975 q) (meaning986 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 986 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 981 = false ∨ valuationOf q 987 = true := by
  have hs : count985 q = (countLit q [-89, -91, -94]) + (countLit q [-95, -97, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94]) (l₂ := [-95, -97, -99, -101])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (981)) (literal (valuationOf q) (987)) (countLit q [-89, -91, -94]) (countLit q [-95, -97, -99, -101]) (count985 q) 2 1 (meaning975 q) (meaning981 q) (meaning987 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 981 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 981 = false ∨ valuation q 987 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 987 = true := by
  have hs : count985 q = (countLit q [-89, -91, -94]) + (countLit q [-95, -97, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94]) (l₂ := [-95, -97, -99, -101])
  have hm := merge_left (literal (valuationOf q) (976)) (literal (valuationOf q) (987)) (countLit q [-89, -91, -94]) (countLit q [-95, -97, -99, -101]) (count985 q) 3 (meaning976 q) (meaning987 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 987 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 981 = false ∨ valuationOf q 988 = true := by
  have hs : count985 q = (countLit q [-89, -91, -94]) + (countLit q [-95, -97, -99, -101]) := List.countP_append (p := literal q) (l₁ := [-89, -91, -94]) (l₂ := [-95, -97, -99, -101])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (981)) (literal (valuationOf q) (988)) (countLit q [-89, -91, -94]) (countLit q [-95, -97, -99, -101]) (count985 q) 3 1 (meaning976 q) (meaning981 q) (meaning988 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 981 = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 981 = false ∨ valuation q 988 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 992 = true := by
  have hs : count992 q = (countLit q [-104]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (992)) (countLit q [-104]) (countLit q [-108]) (count992 q) 1 (meaningNeg108 q) (meaning992 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 992 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 992 = true := by
  have hs : count992 q = (countLit q [-104]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (992)) (countLit q [-104]) (countLit q [-108]) (count992 q) 1 (meaningNeg104 q) (meaning992 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 992 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 108 = true ∨ valuationOf q 993 = true := by
  have hs : count992 q = (countLit q [-104]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (993)) (countLit q [-104]) (countLit q [-108]) (count992 q) 1 1 (meaningNeg104 q) (meaningNeg108 q) (meaning993 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 108 = true ∨ valuation q 993 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 994 = true := by
  have hs : count994 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-109)) (literal (valuationOf q) (994)) (countLit q [-109]) (countLit q [-110]) (count994 q) 1 (meaningNeg109 q) (meaning994 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 994 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 994 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 994 = false ∨ valuationOf q 996 = true := by
  have hs : count996 q = (countLit q [-104, -108]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -108]) (l₂ := [-109, -110])
  have hm := merge_right (literal (valuationOf q) (994)) (literal (valuationOf q) (996)) (countLit q [-104, -108]) (countLit q [-109, -110]) (count996 q) 1 (meaning994 q) (meaning996 q) hs
  change valuationOf q 994 = false ∨ valuationOf q 996 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 994 = false ∨ valuation q 996 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 994 = false ∨ valuationOf q 997 = true := by
  have hs : count996 q = (countLit q [-104, -108]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -108]) (l₂ := [-109, -110])
  have hm := merge_two (literal (valuationOf q) (992)) (literal (valuationOf q) (994)) (literal (valuationOf q) (997)) (countLit q [-104, -108]) (countLit q [-109, -110]) (count996 q) 1 1 (meaning992 q) (meaning994 q) (meaning997 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 994 = false ∨ valuationOf q 997 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 994 = false ∨ valuation q 997 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 994 = false ∨ valuationOf q 998 = true := by
  have hs : count996 q = (countLit q [-104, -108]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -108]) (l₂ := [-109, -110])
  have hm := merge_two (literal (valuationOf q) (993)) (literal (valuationOf q) (994)) (literal (valuationOf q) (998)) (countLit q [-104, -108]) (countLit q [-109, -110]) (count996 q) 2 1 (meaning993 q) (meaning994 q) (meaning998 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 994 = false ∨ valuationOf q 998 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 994 = false ∨ valuation q 998 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1000 = true := by
  have hs : count1000 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1000)) (countLit q [-112]) (countLit q [-113]) (count1000 q) 1 (meaningNeg113 q) (meaning1000 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1000 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E259.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112259
