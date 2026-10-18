import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 123 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [122]) + (countLit q [123]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123])
  have hm := merge_right (literal (valuationOf q) (123)) (literal (valuationOf q) (237)) (countLit q [122]) (countLit q [123]) (count237 q) 1 (meaning123 q) (meaning237 q) hs
  change valuationOf q 123 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 237 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [120, 121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [120, 121]) (l₂ := [122, 123])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [120, 121]) (countLit q [122, 123]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count241 q) 1 (meaning239 q) (meaning241 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (241)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122, 123]) (count241 q) 1 (meaning233 q) (meaning241 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 241 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (243)) (countLit q [111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123]) (count243 q) 1 (meaning229 q) (meaning243 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 243 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 126 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [125]) + (countLit q [126]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126])
  have hm := merge_right (literal (valuationOf q) (126)) (literal (valuationOf q) (245)) (countLit q [125]) (countLit q [126]) (count245 q) 1 (meaning126 q) (meaning245 q) hs
  change valuationOf q 126 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 245 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [124]) + (countLit q [125, 126]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125, 126])
  have hm := merge_right (literal (valuationOf q) (245)) (literal (valuationOf q) (247)) (countLit q [124]) (countLit q [125, 126]) (count247 q) 1 (meaning245 q) (meaning247 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 247 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [124]) + (countLit q [125, 126]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125, 126])
  have hm := merge_left (literal (valuationOf q) (124)) (literal (valuationOf q) (247)) (countLit q [124]) (countLit q [125, 126]) (count247 q) 1 (meaning124 q) (meaning247 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 247 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 245 = false ∨ valuationOf q 248 = true := by
  have hs : count247 q = (countLit q [124]) + (countLit q [125, 126]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125, 126])
  have hm := merge_two (literal (valuationOf q) (124)) (literal (valuationOf q) (245)) (literal (valuationOf q) (248)) (countLit q [124]) (countLit q [125, 126]) (count247 q) 1 1 (meaning124 q) (meaning245 q) (meaning248 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 245 = false ∨ valuationOf q 248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 245 = false ∨ valuation q 248 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_left (literal (valuationOf q) (129)) (literal (valuationOf q) (251)) (countLit q [129]) (countLit q [130]) (count251 q) 1 (meaning129 q) (meaning251 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 251 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [127, 128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [127, 128]) (l₂ := [129, 130])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [127, 128]) (countLit q [129, 130]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (255)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count255 q) 1 (meaning247 q) (meaning255 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 255 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_two (literal (valuationOf q) (247)) (literal (valuationOf q) (253)) (literal (valuationOf q) (256)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count255 q) 1 1 (meaning247 q) (meaning253 q) (meaning256 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 253 = false ∨ valuation q 256 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 248 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129, 130])
  have hm := merge_left (literal (valuationOf q) (248)) (literal (valuationOf q) (256)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129, 130]) (count255 q) 2 (meaning248 q) (meaning256 q) hs
  change valuationOf q 248 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 256 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_right (literal (valuationOf q) (133)) (literal (valuationOf q) (257)) (countLit q [132]) (countLit q [133]) (count257 q) 1 (meaning133 q) (meaning257 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 257 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [131]) + (countLit q [132, 133]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132, 133])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [131]) (countLit q [132, 133]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [131]) + (countLit q [132, 133]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132, 133])
  have hm := merge_left (literal (valuationOf q) (131)) (literal (valuationOf q) (259)) (countLit q [131]) (countLit q [132, 133]) (count259 q) 1 (meaning131 q) (meaning259 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 259 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [134]) + (countLit q [135]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135])
  have hm := merge_left (literal (valuationOf q) (134)) (literal (valuationOf q) (261)) (countLit q [134]) (countLit q [135]) (count261 q) 1 (meaning134 q) (meaning261 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 261 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [136]) + (countLit q [137]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137])
  have hm := merge_left (literal (valuationOf q) (136)) (literal (valuationOf q) (263)) (countLit q [136]) (countLit q [137]) (count263 q) 1 (meaning136 q) (meaning263 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 263 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [134, 135]) + (countLit q [136, 137]) := List.countP_append (p := literal q) (l₁ := [134, 135]) (l₂ := [136, 137])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [134, 135]) (countLit q [136, 137]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [134, 135]) + (countLit q [136, 137]) := List.countP_append (p := literal q) (l₁ := [134, 135]) (l₂ := [136, 137])
  have hm := merge_left (literal (valuationOf q) (261)) (literal (valuationOf q) (265)) (countLit q [134, 135]) (countLit q [136, 137]) (count265 q) 1 (meaning261 q) (meaning265 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 265 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [134, 135]) + (countLit q [136, 137]) := List.countP_append (p := literal q) (l₁ := [134, 135]) (l₂ := [136, 137])
  have hm := merge_two (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (literal (valuationOf q) (266)) (countLit q [134, 135]) (countLit q [136, 137]) (count265 q) 1 1 (meaning261 q) (meaning263 q) (meaning266 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = false ∨ valuation q 266 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [131, 132, 133]) + (countLit q [134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133]) (l₂ := [134, 135, 136, 137])
  have hm := merge_right (literal (valuationOf q) (265)) (literal (valuationOf q) (267)) (countLit q [131, 132, 133]) (countLit q [134, 135, 136, 137]) (count267 q) 1 (meaning265 q) (meaning267 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 267 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 266 = false ∨ valuationOf q 268 = true := by
  have hs : count267 q = (countLit q [131, 132, 133]) + (countLit q [134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133]) (l₂ := [134, 135, 136, 137])
  have hm := merge_right (literal (valuationOf q) (266)) (literal (valuationOf q) (268)) (countLit q [131, 132, 133]) (countLit q [134, 135, 136, 137]) (count267 q) 2 (meaning266 q) (meaning268 q) hs
  change valuationOf q 266 = false ∨ valuationOf q 268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 266 = false ∨ valuation q 268 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [131, 132, 133]) + (countLit q [134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133]) (l₂ := [134, 135, 136, 137])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (267)) (countLit q [131, 132, 133]) (countLit q [134, 135, 136, 137]) (count267 q) 1 (meaning259 q) (meaning267 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 267 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 265 = false ∨ valuationOf q 268 = true := by
  have hs : count267 q = (countLit q [131, 132, 133]) + (countLit q [134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133]) (l₂ := [134, 135, 136, 137])
  have hm := merge_two (literal (valuationOf q) (259)) (literal (valuationOf q) (265)) (literal (valuationOf q) (268)) (countLit q [131, 132, 133]) (countLit q [134, 135, 136, 137]) (count267 q) 1 1 (meaning259 q) (meaning265 q) (meaning268 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 265 = false ∨ valuationOf q 268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 265 = false ∨ valuation q 268 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 268 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137])
  have hm := merge_right (literal (valuationOf q) (268)) (literal (valuationOf q) (270)) (countLit q [124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137]) (count269 q) 2 (meaning268 q) (meaning270 q) hs
  change valuationOf q 268 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 268 = false ∨ valuation q 270 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (269)) (countLit q [124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137]) (count269 q) 1 (meaning255 q) (meaning269 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 269 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137])
  have hm := merge_two (literal (valuationOf q) (255)) (literal (valuationOf q) (267)) (literal (valuationOf q) (270)) (countLit q [124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137]) (count269 q) 1 1 (meaning255 q) (meaning267 q) (meaning270 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 267 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 267 = false ∨ valuation q 270 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 256 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137])
  have hm := merge_left (literal (valuationOf q) (256)) (literal (valuationOf q) (270)) (countLit q [124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137]) (count269 q) 2 (meaning256 q) (meaning270 q) hs
  change valuationOf q 256 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 256 = false ∨ valuation q 270 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E183.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112183
