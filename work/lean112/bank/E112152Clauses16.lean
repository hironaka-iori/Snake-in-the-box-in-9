import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [196, 197, 198]) + (countLit q [199, 200, 201, 202]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198]) (l₂ := [199, 200, 201, 202])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (395)) (countLit q [196, 197, 198]) (countLit q [199, 200, 201, 202]) (count395 q) 1 (meaning387 q) (meaning395 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 395 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [196, 197, 198, 199, 200, 201, 202]) + (countLit q [203, 204, 205, 206, 207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201, 202]) (l₂ := [203, 204, 205, 206, 207, 208, 209, 210])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (411)) (countLit q [196, 197, 198, 199, 200, 201, 202]) (countLit q [203, 204, 205, 206, 207, 208, 209, 210]) (count411 q) 1 (meaning395 q) (meaning411 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 411 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210])
  have hm := merge_right (literal (valuationOf q) (411)) (literal (valuationOf q) (413)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) (count413 q) 1 (meaning411 q) (meaning413 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 413 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210])
  have hm := merge_left (literal (valuationOf q) (383)) (literal (valuationOf q) (413)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) (count413 q) 1 (meaning383 q) (meaning413 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 413 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (415)) (countLit q [212]) (countLit q [213]) (count415 q) 1 (meaning213 q) (meaning415 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 415 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [211]) + (countLit q [212, 213]) := List.countP_append (p := literal q) (l₁ := [211]) (l₂ := [212, 213])
  have hm := merge_right (literal (valuationOf q) (415)) (literal (valuationOf q) (417)) (countLit q [211]) (countLit q [212, 213]) (count417 q) 1 (meaning415 q) (meaning417 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 417 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_right (literal (valuationOf q) (215)) (literal (valuationOf q) (419)) (countLit q [214]) (countLit q [215]) (count419 q) 1 (meaning215 q) (meaning419 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 419 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [216]) + (countLit q [217]) := List.countP_append (p := literal q) (l₁ := [216]) (l₂ := [217])
  have hm := merge_right (literal (valuationOf q) (217)) (literal (valuationOf q) (421)) (countLit q [216]) (countLit q [217]) (count421 q) 1 (meaning217 q) (meaning421 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 421 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_right (literal (valuationOf q) (421)) (literal (valuationOf q) (423)) (countLit q [214, 215]) (countLit q [216, 217]) (count423 q) 1 (meaning421 q) (meaning423 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 423 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (423)) (countLit q [214, 215]) (countLit q [216, 217]) (count423 q) 1 (meaning419 q) (meaning423 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 423 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [211, 212, 213]) (countLit q [214, 215, 216, 217]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (425)) (countLit q [211, 212, 213]) (countLit q [214, 215, 216, 217]) (count425 q) 1 (meaning417 q) (meaning425 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 425 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 218 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [218]) + (countLit q [219]) := List.countP_append (p := literal q) (l₁ := [218]) (l₂ := [219])
  have hm := merge_left (literal (valuationOf q) (218)) (literal (valuationOf q) (427)) (countLit q [218]) (countLit q [219]) (count427 q) 1 (meaning218 q) (meaning427 q) hs
  change valuationOf q 218 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 427 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [218, 219]) + (countLit q [220, 221]) := List.countP_append (p := literal q) (l₁ := [218, 219]) (l₂ := [220, 221])
  have hm := merge_left (literal (valuationOf q) (427)) (literal (valuationOf q) (431)) (countLit q [218, 219]) (countLit q [220, 221]) (count431 q) 1 (meaning427 q) (meaning431 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 431 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [224]) + (countLit q [225]) := List.countP_append (p := literal q) (l₁ := [224]) (l₂ := [225])
  have hm := merge_right (literal (valuationOf q) (225)) (literal (valuationOf q) (435)) (countLit q [224]) (countLit q [225]) (count435 q) 1 (meaning225 q) (meaning435 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 435 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [222, 223]) + (countLit q [224, 225]) := List.countP_append (p := literal q) (l₁ := [222, 223]) (l₂ := [224, 225])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [222, 223]) (countLit q [224, 225]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [218, 219, 220, 221]) + (countLit q [222, 223, 224, 225]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221]) (l₂ := [222, 223, 224, 225])
  have hm := merge_right (literal (valuationOf q) (437)) (literal (valuationOf q) (439)) (countLit q [218, 219, 220, 221]) (countLit q [222, 223, 224, 225]) (count439 q) 1 (meaning437 q) (meaning439 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 439 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [218, 219, 220, 221]) + (countLit q [222, 223, 224, 225]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221]) (l₂ := [222, 223, 224, 225])
  have hm := merge_left (literal (valuationOf q) (431)) (literal (valuationOf q) (439)) (countLit q [218, 219, 220, 221]) (countLit q [222, 223, 224, 225]) (count439 q) 1 (meaning431 q) (meaning439 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 439 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225])
  have hm := merge_right (literal (valuationOf q) (439)) (literal (valuationOf q) (441)) (countLit q [211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225]) (count441 q) 1 (meaning439 q) (meaning441 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 441 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225])
  have hm := merge_left (literal (valuationOf q) (425)) (literal (valuationOf q) (441)) (countLit q [211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225]) (count441 q) 1 (meaning425 q) (meaning441 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 441 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [226]) (l₂ := [227, 228])
  have hm := merge_left (literal (valuationOf q) (226)) (literal (valuationOf q) (445)) (countLit q [226]) (countLit q [227, 228]) (count445 q) 1 (meaning226 q) (meaning445 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 445 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [226, 227, 228]) + (countLit q [229, 230, 231, 232]) := List.countP_append (p := literal q) (l₁ := [226, 227, 228]) (l₂ := [229, 230, 231, 232])
  have hm := merge_left (literal (valuationOf q) (445)) (literal (valuationOf q) (453)) (countLit q [226, 227, 228]) (countLit q [229, 230, 231, 232]) (count453 q) 1 (meaning445 q) (meaning453 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 453 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [239]) + (countLit q [240]) := List.countP_append (p := literal q) (l₁ := [239]) (l₂ := [240])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (463)) (countLit q [239]) (countLit q [240]) (count463 q) 1 (meaning239 q) (meaning463 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 463 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal q) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_right (literal (valuationOf q) (463)) (literal (valuationOf q) (465)) (countLit q [237, 238]) (countLit q [239, 240]) (count465 q) 1 (meaning463 q) (meaning465 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 465 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [233, 234, 235, 236]) + (countLit q [237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236]) (l₂ := [237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (465)) (literal (valuationOf q) (467)) (countLit q [233, 234, 235, 236]) (countLit q [237, 238, 239, 240]) (count467 q) 1 (meaning465 q) (meaning467 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 467 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (467)) (literal (valuationOf q) (469)) (countLit q [226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (count469 q) 1 (meaning467 q) (meaning469 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 469 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (453)) (literal (valuationOf q) (469)) (countLit q [226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (count469 q) 1 (meaning453 q) (meaning469 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 469 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225]) + (countLit q [226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225]) (l₂ := [226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (469)) (literal (valuationOf q) (471)) (countLit q [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225]) (countLit q [226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (count471 q) 1 (meaning469 q) (meaning471 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 471 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225]) + (countLit q [226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225]) (l₂ := [226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (441)) (literal (valuationOf q) (471)) (countLit q [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225]) (countLit q [226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (count471 q) 1 (meaning441 q) (meaning471 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 471 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) + (countLit q [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) (l₂ := [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_right (literal (valuationOf q) (471)) (literal (valuationOf q) (473)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) (countLit q [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (count473 q) 1 (meaning471 q) (meaning473 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 473 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 473 = true := by
  have hs : count473 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) + (countLit q [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) (l₂ := [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_left (literal (valuationOf q) (413)) (literal (valuationOf q) (473)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]) (countLit q [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (count473 q) 1 (meaning413 q) (meaning473 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 473 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true := by
  have hs : count475 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) + (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (l₂ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240])
  have hm := merge_two (literal (valuationOf q) (355)) (literal (valuationOf q) (473)) (literal (valuationOf q) (476)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (count475 q) 1 1 (meaning355 q) (meaning473 q) (meaning476 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 473 = false ∨ valuationOf q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 473 = false ∨ valuation q 476 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E152.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112152
