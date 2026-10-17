import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 248 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [247]) + (countLit q [248]) := List.countP_append (p := literal q) (l₁ := [247]) (l₂ := [248])
  have hm := merge_right (literal (valuationOf q) (248)) (literal (valuationOf q) (481)) (countLit q [247]) (countLit q [248]) (count481 q) 1 (meaning248 q) (meaning481 q) hs
  change valuationOf q 248 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 481 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [247]) + (countLit q [248]) := List.countP_append (p := literal q) (l₁ := [247]) (l₂ := [248])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (481)) (countLit q [247]) (countLit q [248]) (count481 q) 1 (meaning247 q) (meaning481 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 481 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 248 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [247]) + (countLit q [248]) := List.countP_append (p := literal q) (l₁ := [247]) (l₂ := [248])
  have hm := merge_two (literal (valuationOf q) (247)) (literal (valuationOf q) (248)) (literal (valuationOf q) (482)) (countLit q [247]) (countLit q [248]) (count481 q) 1 1 (meaning247 q) (meaning248 q) (meaning482 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 248 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 248 = false ∨ valuation q 482 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [245, 246]) + (countLit q [247, 248]) := List.countP_append (p := literal q) (l₁ := [245, 246]) (l₂ := [247, 248])
  have hm := merge_right (literal (valuationOf q) (481)) (literal (valuationOf q) (483)) (countLit q [245, 246]) (countLit q [247, 248]) (count483 q) 1 (meaning481 q) (meaning483 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 483 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 482 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [245, 246]) + (countLit q [247, 248]) := List.countP_append (p := literal q) (l₁ := [245, 246]) (l₂ := [247, 248])
  have hm := merge_right (literal (valuationOf q) (482)) (literal (valuationOf q) (484)) (countLit q [245, 246]) (countLit q [247, 248]) (count483 q) 2 (meaning482 q) (meaning484 q) hs
  change valuationOf q 482 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 482 = false ∨ valuation q 484 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 483 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (483)) (literal (valuationOf q) (485)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count485 q) 1 (meaning483 q) (meaning485 q) hs
  change valuationOf q 483 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 483 = false ∨ valuation q 485 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 484 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (484)) (literal (valuationOf q) (486)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count485 q) 2 (meaning484 q) (meaning486 q) hs
  change valuationOf q 484 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 484 = false ∨ valuation q 486 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (477)) (literal (valuationOf q) (485)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count485 q) 1 (meaning477 q) (meaning485 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 485 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 477 = false ∨ valuationOf q 483 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (477)) (literal (valuationOf q) (483)) (literal (valuationOf q) (486)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count485 q) 1 1 (meaning477 q) (meaning483 q) (meaning486 q) hs
  change valuationOf q 477 = false ∨ valuationOf q 483 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 483 = false ∨ valuation q 486 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [249]) + (countLit q [250]) := List.countP_append (p := literal q) (l₁ := [249]) (l₂ := [250])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (487)) (countLit q [249]) (countLit q [250]) (count487 q) 1 (meaning249 q) (meaning487 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 487 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 489 = true := by
  have hs : count489 q = (countLit q [251]) + (countLit q [252]) := List.countP_append (p := literal q) (l₁ := [251]) (l₂ := [252])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (489)) (countLit q [251]) (countLit q [252]) (count489 q) 1 (meaning251 q) (meaning489 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 489 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 489 = false ∨ valuationOf q 491 = true := by
  have hs : count491 q = (countLit q [249, 250]) + (countLit q [251, 252]) := List.countP_append (p := literal q) (l₁ := [249, 250]) (l₂ := [251, 252])
  have hm := merge_right (literal (valuationOf q) (489)) (literal (valuationOf q) (491)) (countLit q [249, 250]) (countLit q [251, 252]) (count491 q) 1 (meaning489 q) (meaning491 q) hs
  change valuationOf q 489 = false ∨ valuationOf q 491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 489 = false ∨ valuation q 491 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 491 = true := by
  have hs : count491 q = (countLit q [249, 250]) + (countLit q [251, 252]) := List.countP_append (p := literal q) (l₁ := [249, 250]) (l₂ := [251, 252])
  have hm := merge_left (literal (valuationOf q) (487)) (literal (valuationOf q) (491)) (countLit q [249, 250]) (countLit q [251, 252]) (count491 q) 1 (meaning487 q) (meaning491 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 491 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 495 = true := by
  have hs : count495 q = (countLit q [255]) + (countLit q [256]) := List.countP_append (p := literal q) (l₁ := [255]) (l₂ := [256])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (495)) (countLit q [255]) (countLit q [256]) (count495 q) 1 (meaning255 q) (meaning495 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 495 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 495 = false ∨ valuationOf q 497 = true := by
  have hs : count497 q = (countLit q [253, 254]) + (countLit q [255, 256]) := List.countP_append (p := literal q) (l₁ := [253, 254]) (l₂ := [255, 256])
  have hm := merge_right (literal (valuationOf q) (495)) (literal (valuationOf q) (497)) (countLit q [253, 254]) (countLit q [255, 256]) (count497 q) 1 (meaning495 q) (meaning497 q) hs
  change valuationOf q 495 = false ∨ valuationOf q 497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 495 = false ∨ valuation q 497 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 497 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [249, 250, 251, 252]) + (countLit q [253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [249, 250, 251, 252]) (l₂ := [253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (497)) (literal (valuationOf q) (499)) (countLit q [249, 250, 251, 252]) (countLit q [253, 254, 255, 256]) (count499 q) 1 (meaning497 q) (meaning499 q) hs
  change valuationOf q 497 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 497 = false ∨ valuation q 499 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 491 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [249, 250, 251, 252]) + (countLit q [253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [249, 250, 251, 252]) (l₂ := [253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (491)) (literal (valuationOf q) (499)) (countLit q [249, 250, 251, 252]) (countLit q [253, 254, 255, 256]) (count499 q) 1 (meaning491 q) (meaning499 q) hs
  change valuationOf q 491 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 491 = false ∨ valuation q 499 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 499 = false ∨ valuationOf q 501 = true := by
  have hs : count501 q = (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) + (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244, 245, 246, 247, 248]) (l₂ := [249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (499)) (literal (valuationOf q) (501)) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) (count501 q) 1 (meaning499 q) (meaning501 q) hs
  change valuationOf q 499 = false ∨ valuationOf q 501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 499 = false ∨ valuation q 501 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 485 = false ∨ valuationOf q 501 = true := by
  have hs : count501 q = (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) + (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244, 245, 246, 247, 248]) (l₂ := [249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (485)) (literal (valuationOf q) (501)) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) (count501 q) 1 (meaning485 q) (meaning501 q) hs
  change valuationOf q 485 = false ∨ valuationOf q 501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 485 = false ∨ valuation q 501 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 485 = false ∨ valuationOf q 499 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) + (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244, 245, 246, 247, 248]) (l₂ := [249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_two (literal (valuationOf q) (485)) (literal (valuationOf q) (499)) (literal (valuationOf q) (502)) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) (count501 q) 1 1 (meaning485 q) (meaning499 q) (meaning502 q) hs
  change valuationOf q 485 = false ∨ valuationOf q 499 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 485 = false ∨ valuation q 499 = false ∨ valuation q 502 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 486 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) + (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244, 245, 246, 247, 248]) (l₂ := [249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (486)) (literal (valuationOf q) (502)) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (countLit q [249, 250, 251, 252, 253, 254, 255, 256]) (count501 q) 2 (meaning486 q) (meaning502 q) hs
  change valuationOf q 486 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 486 = false ∨ valuation q 502 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 501 = false ∨ valuationOf q 503 = true := by
  have hs : count503 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (501)) (literal (valuationOf q) (503)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count503 q) 1 (meaning501 q) (meaning503 q) hs
  change valuationOf q 501 = false ∨ valuationOf q 503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 501 = false ∨ valuation q 503 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 502 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (502)) (literal (valuationOf q) (504)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count503 q) 2 (meaning502 q) (meaning504 q) hs
  change valuationOf q 502 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 502 = false ∨ valuation q 504 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 503 = true := by
  have hs : count503 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (471)) (literal (valuationOf q) (503)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count503 q) 1 (meaning471 q) (meaning503 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 503 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 471 = false ∨ valuationOf q 501 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_two (literal (valuationOf q) (471)) (literal (valuationOf q) (501)) (literal (valuationOf q) (504)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count503 q) 1 1 (meaning471 q) (meaning501 q) (meaning504 q) hs
  change valuationOf q 471 = false ∨ valuationOf q 501 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 501 = false ∨ valuation q 504 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 472 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (472)) (literal (valuationOf q) (504)) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count503 q) 2 (meaning472 q) (meaning504 q) hs
  change valuationOf q 472 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 472 = false ∨ valuation q 504 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 503 = false ∨ valuationOf q 505 = true := by
  have hs : count505 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (503)) (literal (valuationOf q) (505)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count505 q) 1 (meaning503 q) (meaning505 q) hs
  change valuationOf q 503 = false ∨ valuationOf q 505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 503 = false ∨ valuation q 505 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 504 = false ∨ valuationOf q 506 = true := by
  have hs : count505 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (504)) (literal (valuationOf q) (506)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count505 q) 2 (meaning504 q) (meaning506 q) hs
  change valuationOf q 504 = false ∨ valuationOf q 506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 504 = false ∨ valuation q 506 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 505 = true := by
  have hs : count505 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (441)) (literal (valuationOf q) (505)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count505 q) 1 (meaning441 q) (meaning505 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 505 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 503 = false ∨ valuationOf q 506 = true := by
  have hs : count505 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_two (literal (valuationOf q) (441)) (literal (valuationOf q) (503)) (literal (valuationOf q) (506)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count505 q) 1 1 (meaning441 q) (meaning503 q) (meaning506 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 503 = false ∨ valuationOf q 506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 503 = false ∨ valuation q 506 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 442 = false ∨ valuationOf q 506 = true := by
  have hs : count505 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (442)) (literal (valuationOf q) (506)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count505 q) 2 (meaning442 q) (meaning506 q) hs
  change valuationOf q 442 = false ∨ valuationOf q 506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 442 = false ∨ valuation q 506 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 506 = false ∨ valuationOf q 508 = true := by
  have hs : count507 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (506)) (literal (valuationOf q) (508)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count507 q) 2 (meaning506 q) (meaning508 q) hs
  change valuationOf q 506 = false ∨ valuationOf q 508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 506 = false ∨ valuation q 508 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E036.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112036
