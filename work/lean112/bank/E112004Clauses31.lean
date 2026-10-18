import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 411 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210])
  have hm := merge_two (literal (valuationOf q) (383)) (literal (valuationOf q) (411)) (literal (valuationOf q) (414)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) (count413 q) 1 1 (meaning383 q) (meaning411 q) (meaning414 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 411 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 411 = false ∨ valuation q 414 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 384 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210])
  have hm := merge_left (literal (valuationOf q) (384)) (literal (valuationOf q) (414)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) (count413 q) 2 (meaning384 q) (meaning414 q) hs
  change valuationOf q 384 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 384 = false ∨ valuation q 414 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (415)) (countLit q [212]) (countLit q [213]) (count415 q) 1 (meaning213 q) (meaning415 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 415 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_left (literal (valuationOf q) (212)) (literal (valuationOf q) (415)) (countLit q [212]) (countLit q [213]) (count415 q) 1 (meaning212 q) (meaning415 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 415 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [211]) + (countLit q [212, 213]) := List.countP_append (p := literal q) (l₁ := [211]) (l₂ := [212, 213])
  have hm := merge_right (literal (valuationOf q) (415)) (literal (valuationOf q) (417)) (countLit q [211]) (countLit q [212, 213]) (count417 q) 1 (meaning415 q) (meaning417 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 417 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_right (literal (valuationOf q) (215)) (literal (valuationOf q) (419)) (countLit q [214]) (countLit q [215]) (count419 q) 1 (meaning215 q) (meaning419 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 419 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 214 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_left (literal (valuationOf q) (214)) (literal (valuationOf q) (419)) (countLit q [214]) (countLit q [215]) (count419 q) 1 (meaning214 q) (meaning419 q) hs
  change valuationOf q 214 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 419 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 216 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [216]) + (countLit q [217]) := List.countP_append (p := literal q) (l₁ := [216]) (l₂ := [217])
  have hm := merge_left (literal (valuationOf q) (216)) (literal (valuationOf q) (421)) (countLit q [216]) (countLit q [217]) (count421 q) 1 (meaning216 q) (meaning421 q) hs
  change valuationOf q 216 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 421 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_right (literal (valuationOf q) (421)) (literal (valuationOf q) (423)) (countLit q [214, 215]) (countLit q [216, 217]) (count423 q) 1 (meaning421 q) (meaning423 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (423)) (countLit q [214, 215]) (countLit q [216, 217]) (count423 q) 1 (meaning419 q) (meaning423 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 423 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [211, 212, 213]) (countLit q [214, 215, 216, 217]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (425)) (countLit q [211, 212, 213]) (countLit q [214, 215, 216, 217]) (count425 q) 1 (meaning417 q) (meaning425 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 425 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 423 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_two (literal (valuationOf q) (417)) (literal (valuationOf q) (423)) (literal (valuationOf q) (426)) (countLit q [211, 212, 213]) (countLit q [214, 215, 216, 217]) (count425 q) 1 1 (meaning417 q) (meaning423 q) (meaning426 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 423 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 423 = false ∨ valuation q 426 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [218]) + (countLit q [219]) := List.countP_append (p := literal q) (l₁ := [218]) (l₂ := [219])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (427)) (countLit q [218]) (countLit q [219]) (count427 q) 1 (meaning219 q) (meaning427 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 427 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 220 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [220]) + (countLit q [221]) := List.countP_append (p := literal q) (l₁ := [220]) (l₂ := [221])
  have hm := merge_left (literal (valuationOf q) (220)) (literal (valuationOf q) (429)) (countLit q [220]) (countLit q [221]) (count429 q) 1 (meaning220 q) (meaning429 q) hs
  change valuationOf q 220 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 429 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [218, 219]) + (countLit q [220, 221]) := List.countP_append (p := literal q) (l₁ := [218, 219]) (l₂ := [220, 221])
  have hm := merge_right (literal (valuationOf q) (429)) (literal (valuationOf q) (431)) (countLit q [218, 219]) (countLit q [220, 221]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [218, 219]) + (countLit q [220, 221]) := List.countP_append (p := literal q) (l₁ := [218, 219]) (l₂ := [220, 221])
  have hm := merge_left (literal (valuationOf q) (427)) (literal (valuationOf q) (431)) (countLit q [218, 219]) (countLit q [220, 221]) (count431 q) 1 (meaning427 q) (meaning431 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 431 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 224 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [224]) + (countLit q [225]) := List.countP_append (p := literal q) (l₁ := [224]) (l₂ := [225])
  have hm := merge_left (literal (valuationOf q) (224)) (literal (valuationOf q) (435)) (countLit q [224]) (countLit q [225]) (count435 q) 1 (meaning224 q) (meaning435 q) hs
  change valuationOf q 224 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 224 = false ∨ valuation q 435 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [222, 223]) + (countLit q [224, 225]) := List.countP_append (p := literal q) (l₁ := [222, 223]) (l₂ := [224, 225])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [222, 223]) (countLit q [224, 225]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [218, 219, 220, 221]) + (countLit q [222, 223, 224, 225]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221]) (l₂ := [222, 223, 224, 225])
  have hm := merge_right (literal (valuationOf q) (437)) (literal (valuationOf q) (439)) (countLit q [218, 219, 220, 221]) (countLit q [222, 223, 224, 225]) (count439 q) 1 (meaning437 q) (meaning439 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 439 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [218, 219, 220, 221]) + (countLit q [222, 223, 224, 225]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221]) (l₂ := [222, 223, 224, 225])
  have hm := merge_left (literal (valuationOf q) (431)) (literal (valuationOf q) (439)) (countLit q [218, 219, 220, 221]) (countLit q [222, 223, 224, 225]) (count439 q) 1 (meaning431 q) (meaning439 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 439 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225])
  have hm := merge_right (literal (valuationOf q) (439)) (literal (valuationOf q) (441)) (countLit q [211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225]) (count441 q) 1 (meaning439 q) (meaning441 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 441 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (441)) (countLit q [211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225]) (count441 q) 1 (meaning425 q) (meaning441 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 441 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 439 = false ∨ valuationOf q 442 = true := by
  have hs : count441 q = (countLit q [211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225])
  have hm := merge_two (literal (valuationOf q) (425)) (literal (valuationOf q) (439)) (literal (valuationOf q) (442)) (countLit q [211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225]) (count441 q) 1 1 (meaning425 q) (meaning439 q) (meaning442 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 439 = false ∨ valuationOf q 442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 439 = false ∨ valuation q 442 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 426 = false ∨ valuationOf q 442 = true := by
  have hs : count441 q = (countLit q [211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225])
  have hm := merge_left (literal (valuationOf q) (426)) (literal (valuationOf q) (442)) (countLit q [211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225]) (count441 q) 2 (meaning426 q) (meaning442 q) hs
  change valuationOf q 426 = false ∨ valuationOf q 442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 426 = false ∨ valuation q 442 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [227]) + (countLit q [228]) := List.countP_append (p := literal q) (l₁ := [227]) (l₂ := [228])
  have hm := merge_left (literal (valuationOf q) (227)) (literal (valuationOf q) (443)) (countLit q [227]) (countLit q [228]) (count443 q) 1 (meaning227 q) (meaning443 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 443 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [226]) (l₂ := [227, 228])
  have hm := merge_right (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (countLit q [226]) (countLit q [227, 228]) (count445 q) 1 (meaning443 q) (meaning445 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 230 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [229]) + (countLit q [230]) := List.countP_append (p := literal q) (l₁ := [229]) (l₂ := [230])
  have hm := merge_right (literal (valuationOf q) (230)) (literal (valuationOf q) (447)) (countLit q [229]) (countLit q [230]) (count447 q) 1 (meaning230 q) (meaning447 q) hs
  change valuationOf q 230 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 447 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 232 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [231]) + (countLit q [232]) := List.countP_append (p := literal q) (l₁ := [231]) (l₂ := [232])
  have hm := merge_right (literal (valuationOf q) (232)) (literal (valuationOf q) (449)) (countLit q [231]) (countLit q [232]) (count449 q) 1 (meaning232 q) (meaning449 q) hs
  change valuationOf q 232 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 449 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_right (literal (valuationOf q) (449)) (literal (valuationOf q) (451)) (countLit q [229, 230]) (countLit q [231, 232]) (count451 q) 1 (meaning449 q) (meaning451 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 451 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_left (literal (valuationOf q) (447)) (literal (valuationOf q) (451)) (countLit q [229, 230]) (countLit q [231, 232]) (count451 q) 1 (meaning447 q) (meaning451 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 451 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [226, 227, 228]) + (countLit q [229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [226, 227, 228]) (l₂ := [229, 230, 231, 232])
  have hm := merge_right (literal (valuationOf q) (451)) (literal (valuationOf q) (453)) (countLit q [226, 227, 228]) (countLit q [229, 230, 231, 232]) (count453 q) 1 (meaning451 q) (meaning453 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 453 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E004.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112004
