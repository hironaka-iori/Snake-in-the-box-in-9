import E112249Semantics
import B112E249Inputs
namespace Snake9.Regrowth.E112249
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-23]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-27])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (1306)) (countLit q [-23]) (countLit q [-27]) (count1306 q) 1 (meaningNeg23 q) (meaning1306 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1306 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 1306 = false ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-21]) + (countLit q [-23, -27]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23, -27])
  have hm := merge_right (literal (valuationOf q) (1306)) (literal (valuationOf q) (1308)) (countLit q [-21]) (countLit q [-23, -27]) (count1308 q) 1 (meaning1306 q) (meaning1308 q) hs
  change valuationOf q 1306 = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 1306 = false ∨ valuation q 1308 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-21]) + (countLit q [-23, -27]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23, -27])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1308)) (countLit q [-21]) (countLit q [-23, -27]) (count1308 q) 1 (meaningNeg21 q) (meaning1308 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1308 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-14, -18, -20]) + (countLit q [-21, -23, -27]) := List.countP_append (p := literal q) (l₁ := [-14, -18, -20]) (l₂ := [-21, -23, -27])
  have hm := merge_right (literal (valuationOf q) (1308)) (literal (valuationOf q) (1311)) (countLit q [-14, -18, -20]) (countLit q [-21, -23, -27]) (count1311 q) 1 (meaning1308 q) (meaning1311 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1311 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 1303 = false ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-14, -18, -20]) + (countLit q [-21, -23, -27]) := List.countP_append (p := literal q) (l₁ := [-14, -18, -20]) (l₂ := [-21, -23, -27])
  have hm := merge_left (literal (valuationOf q) (1303)) (literal (valuationOf q) (1311)) (countLit q [-14, -18, -20]) (countLit q [-21, -23, -27]) (count1311 q) 1 (meaning1303 q) (meaning1311 q) hs
  change valuationOf q 1303 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 1303 = false ∨ valuation q 1311 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 1295 = false ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-2, -5, -7, -11, -12, -13]) + (countLit q [-14, -18, -20, -21, -23, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13]) (l₂ := [-14, -18, -20, -21, -23, -27])
  have hm := merge_left (literal (valuationOf q) (1295)) (literal (valuationOf q) (1317)) (countLit q [-2, -5, -7, -11, -12, -13]) (countLit q [-14, -18, -20, -21, -23, -27]) (count1317 q) 1 (meaning1295 q) (meaning1317 q) hs
  change valuationOf q 1295 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 1295 = false ∨ valuation q 1317 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 1295 = false ∨ valuationOf q 1311 = false ∨ valuationOf q 1318 = true := by
  have hs : count1317 q = (countLit q [-2, -5, -7, -11, -12, -13]) + (countLit q [-14, -18, -20, -21, -23, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13]) (l₂ := [-14, -18, -20, -21, -23, -27])
  have hm := merge_two (literal (valuationOf q) (1295)) (literal (valuationOf q) (1311)) (literal (valuationOf q) (1318)) (countLit q [-2, -5, -7, -11, -12, -13]) (countLit q [-14, -18, -20, -21, -23, -27]) (count1317 q) 1 1 (meaning1295 q) (meaning1311 q) (meaning1318 q) hs
  change valuationOf q 1295 = false ∨ valuationOf q 1311 = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 1295 = false ∨ valuation q 1311 = false ∨ valuation q 1318 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1318 = true := by
  have hs : count1317 q = (countLit q [-2, -5, -7, -11, -12, -13]) + (countLit q [-14, -18, -20, -21, -23, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13]) (l₂ := [-14, -18, -20, -21, -23, -27])
  have hm := merge_left (literal (valuationOf q) (1296)) (literal (valuationOf q) (1318)) (countLit q [-2, -5, -7, -11, -12, -13]) (countLit q [-14, -18, -20, -21, -23, -27]) (count1317 q) 2 (meaning1296 q) (meaning1318 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1318 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1311 = false ∨ valuationOf q 1319 = true := by
  have hs : count1317 q = (countLit q [-2, -5, -7, -11, -12, -13]) + (countLit q [-14, -18, -20, -21, -23, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13]) (l₂ := [-14, -18, -20, -21, -23, -27])
  have hm := merge_two (literal (valuationOf q) (1296)) (literal (valuationOf q) (1311)) (literal (valuationOf q) (1319)) (countLit q [-2, -5, -7, -11, -12, -13]) (countLit q [-14, -18, -20, -21, -23, -27]) (count1317 q) 2 1 (meaning1296 q) (meaning1311 q) (meaning1319 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1311 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1311 = false ∨ valuation q 1319 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (1326)) (countLit q [-29]) (countLit q [-30]) (count1326 q) 1 (meaningNeg30 q) (meaning1326 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1326 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1326)) (countLit q [-29]) (countLit q [-30]) (count1326 q) 1 (meaningNeg29 q) (meaning1326 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1326 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1328 = true := by
  have hs : count1328 q = (countLit q [-28]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (1326)) (literal (valuationOf q) (1328)) (countLit q [-28]) (countLit q [-29, -30]) (count1328 q) 1 (meaning1326 q) (meaning1328 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1328 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1328 = true := by
  have hs : count1328 q = (countLit q [-28]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -30])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1328)) (countLit q [-28]) (countLit q [-29, -30]) (count1328 q) 1 (meaningNeg28 q) (meaning1328 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1328 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1331 = true := by
  have hs : count1331 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1331)) (countLit q [-38]) (countLit q [-40]) (count1331 q) 1 (meaningNeg40 q) (meaning1331 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1331 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1331 = true := by
  have hs : count1331 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1331)) (countLit q [-38]) (countLit q [-40]) (count1331 q) 1 (meaningNeg38 q) (meaning1331 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1331 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 40 = true ∨ valuationOf q 1332 = true := by
  have hs : count1331 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (-40)) (literal (valuationOf q) (1332)) (countLit q [-38]) (countLit q [-40]) (count1331 q) 1 1 (meaningNeg38 q) (meaningNeg40 q) (meaning1332 q) hs
  change (! (valuationOf q 38)) = false ∨ (! (valuationOf q 40)) = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 1332 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1333 = true := by
  have hs : count1333 q = (countLit q [-34]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1331)) (literal (valuationOf q) (1333)) (countLit q [-34]) (countLit q [-38, -40]) (count1333 q) 1 (meaning1331 q) (meaning1333 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1333 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1334 = true := by
  have hs : count1333 q = (countLit q [-34]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1332)) (literal (valuationOf q) (1334)) (countLit q [-34]) (countLit q [-38, -40]) (count1333 q) 2 (meaning1332 q) (meaning1334 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1334 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1336 = true := by
  have hs : count1336 q = (countLit q [-28, -29, -30]) + (countLit q [-34, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30]) (l₂ := [-34, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1328)) (literal (valuationOf q) (1336)) (countLit q [-28, -29, -30]) (countLit q [-34, -38, -40]) (count1336 q) 1 (meaning1328 q) (meaning1336 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1336 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1337 = true := by
  have hs : count1336 q = (countLit q [-28, -29, -30]) + (countLit q [-34, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30]) (l₂ := [-34, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1333)) (literal (valuationOf q) (1337)) (countLit q [-28, -29, -30]) (countLit q [-34, -38, -40]) (count1336 q) 1 1 (meaning1328 q) (meaning1333 q) (meaning1337 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1333 = false ∨ valuation q 1337 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1338 = true := by
  have hs : count1336 q = (countLit q [-28, -29, -30]) + (countLit q [-34, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30]) (l₂ := [-34, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1334)) (literal (valuationOf q) (1338)) (countLit q [-28, -29, -30]) (countLit q [-34, -38, -40]) (count1336 q) 1 2 (meaning1328 q) (meaning1334 q) (meaning1338 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1334 = false ∨ valuation q 1338 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1342 = true := by
  have hs : count1342 q = (countLit q [-42]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1342)) (countLit q [-42]) (countLit q [-48]) (count1342 q) 1 (meaningNeg48 q) (meaning1342 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1342 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1342 = true := by
  have hs : count1342 q = (countLit q [-42]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1342)) (countLit q [-42]) (countLit q [-48]) (count1342 q) 1 (meaningNeg42 q) (meaning1342 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1342 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 48 = true ∨ valuationOf q 1343 = true := by
  have hs : count1342 q = (countLit q [-42]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (1343)) (countLit q [-42]) (countLit q [-48]) (count1342 q) 1 1 (meaningNeg42 q) (meaningNeg48 q) (meaning1343 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 48 = true ∨ valuation q 1343 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-41]) + (countLit q [-42, -48]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -48])
  have hm := merge_right (literal (valuationOf q) (1342)) (literal (valuationOf q) (1344)) (countLit q [-41]) (countLit q [-42, -48]) (count1344 q) 1 (meaning1342 q) (meaning1344 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1344 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1345 = true := by
  have hs : count1344 q = (countLit q [-41]) + (countLit q [-42, -48]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -48])
  have hm := merge_right (literal (valuationOf q) (1343)) (literal (valuationOf q) (1345)) (countLit q [-41]) (countLit q [-42, -48]) (count1344 q) 2 (meaning1343 q) (meaning1345 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1345 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-41]) + (countLit q [-42, -48]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -48])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1344)) (countLit q [-41]) (countLit q [-42, -48]) (count1344 q) 1 (meaningNeg41 q) (meaning1344 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1344 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1342 = false ∨ valuationOf q 1345 = true := by
  have hs : count1344 q = (countLit q [-41]) + (countLit q [-42, -48]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -48])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (1342)) (literal (valuationOf q) (1345)) (countLit q [-41]) (countLit q [-42, -48]) (count1344 q) 1 1 (meaningNeg41 q) (meaning1342 q) (meaning1345 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1342 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1342 = false ∨ valuation q 1345 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1343 = false ∨ valuationOf q 1346 = true := by
  have hs : count1344 q = (countLit q [-41]) + (countLit q [-42, -48]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -48])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (1343)) (literal (valuationOf q) (1346)) (countLit q [-41]) (countLit q [-42, -48]) (count1344 q) 1 2 (meaningNeg41 q) (meaning1343 q) (meaning1346 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1343 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1343 = false ∨ valuation q 1346 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1347 = true := by
  have hs : count1347 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1347)) (countLit q [-51]) (countLit q [-52]) (count1347 q) 1 (meaningNeg52 q) (meaning1347 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1347 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1347 = true := by
  have hs : count1347 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (1347)) (countLit q [-51]) (countLit q [-52]) (count1347 q) 1 (meaningNeg51 q) (meaning1347 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1347 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 52 = true ∨ valuationOf q 1348 = true := by
  have hs : count1347 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (1348)) (countLit q [-51]) (countLit q [-52]) (count1347 q) 1 1 (meaningNeg51 q) (meaningNeg52 q) (meaning1348 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 1348 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E249.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112249
