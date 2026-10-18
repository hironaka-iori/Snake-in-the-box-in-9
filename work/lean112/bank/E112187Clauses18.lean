import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207])
  have hm := merge_two (literal (valuationOf q) (379)) (literal (valuationOf q) (407)) (literal (valuationOf q) (410)) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (count409 q) 1 1 (meaning379 q) (meaning407 q) (meaning410 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 407 = false ∨ valuation q 410 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 380 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207])
  have hm := merge_left (literal (valuationOf q) (380)) (literal (valuationOf q) (410)) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]) (count409 q) 2 (meaning380 q) (meaning410 q) hs
  change valuationOf q 380 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 380 = false ∨ valuation q 410 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_left (literal (valuationOf q) (209)) (literal (valuationOf q) (411)) (countLit q [209]) (countLit q [210]) (count411 q) 1 (meaning209 q) (meaning411 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 411 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [208]) + (countLit q [209, 210]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209, 210])
  have hm := merge_right (literal (valuationOf q) (411)) (literal (valuationOf q) (413)) (countLit q [208]) (countLit q [209, 210]) (count413 q) 1 (meaning411 q) (meaning413 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 413 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 214 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [213]) + (countLit q [214]) := List.countP_append (p := literal q) (l₁ := [213]) (l₂ := [214])
  have hm := merge_right (literal (valuationOf q) (214)) (literal (valuationOf q) (417)) (countLit q [213]) (countLit q [214]) (count417 q) 1 (meaning214 q) (meaning417 q) hs
  change valuationOf q 214 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 417 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [211, 212]) + (countLit q [213, 214]) := List.countP_append (p := literal q) (l₁ := [211, 212]) (l₂ := [213, 214])
  have hm := merge_right (literal (valuationOf q) (417)) (literal (valuationOf q) (419)) (countLit q [211, 212]) (countLit q [213, 214]) (count419 q) 1 (meaning417 q) (meaning419 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 419 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [208, 209, 210]) + (countLit q [211, 212, 213, 214]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210]) (l₂ := [211, 212, 213, 214])
  have hm := merge_right (literal (valuationOf q) (419)) (literal (valuationOf q) (421)) (countLit q [208, 209, 210]) (countLit q [211, 212, 213, 214]) (count421 q) 1 (meaning419 q) (meaning421 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 421 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [208, 209, 210]) + (countLit q [211, 212, 213, 214]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210]) (l₂ := [211, 212, 213, 214])
  have hm := merge_left (literal (valuationOf q) (413)) (literal (valuationOf q) (421)) (countLit q [208, 209, 210]) (countLit q [211, 212, 213, 214]) (count421 q) 1 (meaning413 q) (meaning421 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 421 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 419 = false ∨ valuationOf q 422 = true := by
  have hs : count421 q = (countLit q [208, 209, 210]) + (countLit q [211, 212, 213, 214]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210]) (l₂ := [211, 212, 213, 214])
  have hm := merge_two (literal (valuationOf q) (413)) (literal (valuationOf q) (419)) (literal (valuationOf q) (422)) (countLit q [208, 209, 210]) (countLit q [211, 212, 213, 214]) (count421 q) 1 1 (meaning413 q) (meaning419 q) (meaning422 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 419 = false ∨ valuationOf q 422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 419 = false ∨ valuation q 422 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 216 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [215]) + (countLit q [216]) := List.countP_append (p := literal q) (l₁ := [215]) (l₂ := [216])
  have hm := merge_right (literal (valuationOf q) (216)) (literal (valuationOf q) (423)) (countLit q [215]) (countLit q [216]) (count423 q) 1 (meaning216 q) (meaning423 q) hs
  change valuationOf q 216 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 423 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (425)) (countLit q [217]) (countLit q [218]) (count425 q) 1 (meaning217 q) (meaning425 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 425 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [215, 216]) + (countLit q [217, 218]) := List.countP_append (p := literal q) (l₁ := [215, 216]) (l₂ := [217, 218])
  have hm := merge_right (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (countLit q [215, 216]) (countLit q [217, 218]) (count427 q) 1 (meaning425 q) (meaning427 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [215, 216]) + (countLit q [217, 218]) := List.countP_append (p := literal q) (l₁ := [215, 216]) (l₂ := [217, 218])
  have hm := merge_left (literal (valuationOf q) (423)) (literal (valuationOf q) (427)) (countLit q [215, 216]) (countLit q [217, 218]) (count427 q) 1 (meaning423 q) (meaning427 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 427 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 220 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [219]) + (countLit q [220]) := List.countP_append (p := literal q) (l₁ := [219]) (l₂ := [220])
  have hm := merge_right (literal (valuationOf q) (220)) (literal (valuationOf q) (429)) (countLit q [219]) (countLit q [220]) (count429 q) 1 (meaning220 q) (meaning429 q) hs
  change valuationOf q 220 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 429 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [219, 220]) + (countLit q [221, 222]) := List.countP_append (p := literal q) (l₁ := [219, 220]) (l₂ := [221, 222])
  have hm := merge_left (literal (valuationOf q) (429)) (literal (valuationOf q) (433)) (countLit q [219, 220]) (countLit q [221, 222]) (count433 q) 1 (meaning429 q) (meaning433 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 433 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [215, 216, 217, 218]) + (countLit q [219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [215, 216, 217, 218]) (l₂ := [219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (433)) (literal (valuationOf q) (435)) (countLit q [215, 216, 217, 218]) (countLit q [219, 220, 221, 222]) (count435 q) 1 (meaning433 q) (meaning435 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 435 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [215, 216, 217, 218]) + (countLit q [219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [215, 216, 217, 218]) (l₂ := [219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (427)) (literal (valuationOf q) (435)) (countLit q [215, 216, 217, 218]) (countLit q [219, 220, 221, 222]) (count435 q) 1 (meaning427 q) (meaning435 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 435 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [208, 209, 210, 211, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [208, 209, 210, 211, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [208, 209, 210, 211, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (421)) (literal (valuationOf q) (437)) (countLit q [208, 209, 210, 211, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 (meaning421 q) (meaning437 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 437 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 435 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [208, 209, 210, 211, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_two (literal (valuationOf q) (421)) (literal (valuationOf q) (435)) (literal (valuationOf q) (438)) (countLit q [208, 209, 210, 211, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 1 (meaning421 q) (meaning435 q) (meaning438 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 435 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 435 = false ∨ valuation q 438 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 422 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [208, 209, 210, 211, 212, 213, 214]) + (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211, 212, 213, 214]) (l₂ := [215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (422)) (literal (valuationOf q) (438)) (countLit q [208, 209, 210, 211, 212, 213, 214]) (countLit q [215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 2 (meaning422 q) (meaning438 q) hs
  change valuationOf q 422 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 422 = false ∨ valuation q 438 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [223]) + (countLit q [224, 225]) := List.countP_append (p := literal q) (l₁ := [223]) (l₂ := [224, 225])
  have hm := merge_left (literal (valuationOf q) (223)) (literal (valuationOf q) (441)) (countLit q [223]) (countLit q [224, 225]) (count441 q) 1 (meaning223 q) (meaning441 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 441 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [226]) + (countLit q [227]) := List.countP_append (p := literal q) (l₁ := [226]) (l₂ := [227])
  have hm := merge_right (literal (valuationOf q) (227)) (literal (valuationOf q) (443)) (countLit q [226]) (countLit q [227]) (count443 q) 1 (meaning227 q) (meaning443 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 443 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [226]) + (countLit q [227]) := List.countP_append (p := literal q) (l₁ := [226]) (l₂ := [227])
  have hm := merge_left (literal (valuationOf q) (226)) (literal (valuationOf q) (443)) (countLit q [226]) (countLit q [227]) (count443 q) 1 (meaning226 q) (meaning443 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 443 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 227 = false ∨ valuationOf q 444 = true := by
  have hs : count443 q = (countLit q [226]) + (countLit q [227]) := List.countP_append (p := literal q) (l₁ := [226]) (l₂ := [227])
  have hm := merge_two (literal (valuationOf q) (226)) (literal (valuationOf q) (227)) (literal (valuationOf q) (444)) (countLit q [226]) (countLit q [227]) (count443 q) 1 1 (meaning226 q) (meaning227 q) (meaning444 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 227 = false ∨ valuationOf q 444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 227 = false ∨ valuation q 444 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [228]) + (countLit q [229]) := List.countP_append (p := literal q) (l₁ := [228]) (l₂ := [229])
  have hm := merge_left (literal (valuationOf q) (228)) (literal (valuationOf q) (445)) (countLit q [228]) (countLit q [229]) (count445 q) 1 (meaning228 q) (meaning445 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 445 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [226, 227]) + (countLit q [228, 229]) := List.countP_append (p := literal q) (l₁ := [226, 227]) (l₂ := [228, 229])
  have hm := merge_right (literal (valuationOf q) (445)) (literal (valuationOf q) (447)) (countLit q [226, 227]) (countLit q [228, 229]) (count447 q) 1 (meaning445 q) (meaning447 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 447 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [226, 227]) + (countLit q [228, 229]) := List.countP_append (p := literal q) (l₁ := [226, 227]) (l₂ := [228, 229])
  have hm := merge_left (literal (valuationOf q) (443)) (literal (valuationOf q) (447)) (countLit q [226, 227]) (countLit q [228, 229]) (count447 q) 1 (meaning443 q) (meaning447 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 447 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = false ∨ valuationOf q 448 = true := by
  have hs : count447 q = (countLit q [226, 227]) + (countLit q [228, 229]) := List.countP_append (p := literal q) (l₁ := [226, 227]) (l₂ := [228, 229])
  have hm := merge_two (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (literal (valuationOf q) (448)) (countLit q [226, 227]) (countLit q [228, 229]) (count447 q) 1 1 (meaning443 q) (meaning445 q) (meaning448 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = false ∨ valuationOf q 448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = false ∨ valuation q 448 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 444 = false ∨ valuationOf q 448 = true := by
  have hs : count447 q = (countLit q [226, 227]) + (countLit q [228, 229]) := List.countP_append (p := literal q) (l₁ := [226, 227]) (l₂ := [228, 229])
  have hm := merge_left (literal (valuationOf q) (444)) (literal (valuationOf q) (448)) (countLit q [226, 227]) (countLit q [228, 229]) (count447 q) 2 (meaning444 q) (meaning448 q) hs
  change valuationOf q 444 = false ∨ valuationOf q 448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 444 = false ∨ valuation q 448 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [223, 224, 225]) + (countLit q [226, 227, 228, 229]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225]) (l₂ := [226, 227, 228, 229])
  have hm := merge_right (literal (valuationOf q) (447)) (literal (valuationOf q) (449)) (countLit q [223, 224, 225]) (countLit q [226, 227, 228, 229]) (count449 q) 1 (meaning447 q) (meaning449 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 449 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 448 = false ∨ valuationOf q 450 = true := by
  have hs : count449 q = (countLit q [223, 224, 225]) + (countLit q [226, 227, 228, 229]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225]) (l₂ := [226, 227, 228, 229])
  have hm := merge_right (literal (valuationOf q) (448)) (literal (valuationOf q) (450)) (countLit q [223, 224, 225]) (countLit q [226, 227, 228, 229]) (count449 q) 2 (meaning448 q) (meaning450 q) hs
  change valuationOf q 448 = false ∨ valuationOf q 450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 448 = false ∨ valuation q 450 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E187.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112187
