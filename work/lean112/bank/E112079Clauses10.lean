import E112079Semantics
import B112E079Inputs
namespace Snake9.Regrowth.E112079
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 214 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [214]) + (countLit q [215, 216]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215, 216])
  have hm := merge_left (literal (valuationOf q) (214)) (literal (valuationOf q) (419)) (countLit q [214]) (countLit q [215, 216]) (count419 q) 1 (meaning214 q) (meaning419 q) hs
  change valuationOf q 214 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 419 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 218 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_right (literal (valuationOf q) (218)) (literal (valuationOf q) (421)) (countLit q [217]) (countLit q [218]) (count421 q) 1 (meaning218 q) (meaning421 q) hs
  change valuationOf q 218 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 421 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (421)) (countLit q [217]) (countLit q [218]) (count421 q) 1 (meaning217 q) (meaning421 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 421 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [217, 218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [217, 218]) (l₂ := [219, 220])
  have hm := merge_left (literal (valuationOf q) (421)) (literal (valuationOf q) (425)) (countLit q [217, 218]) (countLit q [219, 220]) (count425 q) 1 (meaning421 q) (meaning425 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 425 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [214, 215, 216]) + (countLit q [217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216]) (l₂ := [217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (countLit q [214, 215, 216]) (countLit q [217, 218, 219, 220]) (count427 q) 1 (meaning425 q) (meaning427 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [214, 215, 216]) + (countLit q [217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216]) (l₂ := [217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (427)) (countLit q [214, 215, 216]) (countLit q [217, 218, 219, 220]) (count427 q) 1 (meaning419 q) (meaning427 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 427 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [214, 215, 216]) + (countLit q [217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216]) (l₂ := [217, 218, 219, 220])
  have hm := merge_two (literal (valuationOf q) (419)) (literal (valuationOf q) (425)) (literal (valuationOf q) (428)) (countLit q [214, 215, 216]) (countLit q [217, 218, 219, 220]) (count427 q) 1 1 (meaning419 q) (meaning425 q) (meaning428 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 425 = false ∨ valuation q 428 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 428 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (428)) (literal (valuationOf q) (430)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220]) (count429 q) 2 (meaning428 q) (meaning430 q) hs
  change valuationOf q 428 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 428 = false ∨ valuation q 430 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (415)) (literal (valuationOf q) (429)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220]) (count429 q) 1 (meaning415 q) (meaning429 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 429 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 416 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (416)) (literal (valuationOf q) (430)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220]) (count429 q) 2 (meaning416 q) (meaning430 q) hs
  change valuationOf q 416 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 416 = false ∨ valuation q 430 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (429)) (literal (valuationOf q) (431)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 430 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (430)) (literal (valuationOf q) (432)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 2 (meaning430 q) (meaning432 q) hs
  change valuationOf q 430 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 430 = false ∨ valuation q 432 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (403)) (literal (valuationOf q) (431)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 1 (meaning403 q) (meaning431 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 431 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_two (literal (valuationOf q) (403)) (literal (valuationOf q) (429)) (literal (valuationOf q) (432)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 1 1 (meaning403 q) (meaning429 q) (meaning432 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 429 = false ∨ valuation q 432 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (404)) (literal (valuationOf q) (432)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 2 (meaning404 q) (meaning432 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 432 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (431)) (literal (valuationOf q) (433)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 1 (meaning431 q) (meaning433 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 433 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 432 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (432)) (literal (valuationOf q) (434)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 2 (meaning432 q) (meaning434 q) hs
  change valuationOf q 432 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 432 = false ∨ valuation q 434 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (377)) (literal (valuationOf q) (433)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 1 (meaning377 q) (meaning433 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 433 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (378)) (literal (valuationOf q) (434)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 2 (meaning378 q) (meaning434 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 434 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 434 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (434)) (literal (valuationOf q) (436)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count435 q) 2 (meaning434 q) (meaning436 q) hs
  change valuationOf q 434 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 434 = false ∨ valuation q 436 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_two (literal (valuationOf q) (325)) (literal (valuationOf q) (433)) (literal (valuationOf q) (436)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count435 q) 1 1 (meaning325 q) (meaning433 q) (meaning436 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 433 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 433 = false ∨ valuation q 436 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 326 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (326)) (literal (valuationOf q) (436)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count435 q) 2 (meaning326 q) (meaning436 q) hs
  change valuationOf q 326 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 326 = false ∨ valuation q 436 = true := counterClause343 (baseVal q)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 436 = false := by
  rw [value436]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count435 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause345 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1333 = true := by
  have hs : count1333 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1333)) (countLit q [-4]) (countLit q [-5]) (count1333 q) 1 (meaningNeg5 q) (meaning1333 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1333 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1333 = true := by
  have hs : count1333 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1333)) (countLit q [-4]) (countLit q [-5]) (count1333 q) 1 (meaningNeg4 q) (meaning1333 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1333 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1335 = true := by
  have hs : count1335 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (1333)) (literal (valuationOf q) (1335)) (countLit q [-2]) (countLit q [-4, -5]) (count1335 q) 1 (meaning1333 q) (meaning1335 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1335 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1335 = true := by
  have hs : count1335 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1335)) (countLit q [-2]) (countLit q [-4, -5]) (count1335 q) 1 (meaningNeg2 q) (meaning1335 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1335 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (1338)) (countLit q [-10]) (countLit q [-11]) (count1338 q) 1 (meaningNeg11 q) (meaning1338 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1338 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1338)) (countLit q [-10]) (countLit q [-11]) (count1338 q) 1 (meaningNeg10 q) (meaning1338 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1338 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 11 = true ∨ valuationOf q 1339 = true := by
  have hs : count1338 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (-11)) (literal (valuationOf q) (1339)) (countLit q [-10]) (countLit q [-11]) (count1338 q) 1 1 (meaningNeg10 q) (meaningNeg11 q) (meaning1339 q) hs
  change (! (valuationOf q 10)) = false ∨ (! (valuationOf q 11)) = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 11 = true ∨ valuation q 1339 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-7]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-10, -11])
  have hm := merge_right (literal (valuationOf q) (1338)) (literal (valuationOf q) (1340)) (countLit q [-7]) (countLit q [-10, -11]) (count1340 q) 1 (meaning1338 q) (meaning1340 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1340 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E079.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112079
