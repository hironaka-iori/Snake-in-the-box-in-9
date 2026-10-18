import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 902 = true := by
  have hs : count902 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (902)) (countLit q [-71]) (countLit q [-73]) (count902 q) 1 (meaningNeg71 q) (meaning902 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 902 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 73 = true ∨ valuationOf q 903 = true := by
  have hs : count902 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (903)) (countLit q [-71]) (countLit q [-73]) (count902 q) 1 1 (meaningNeg71 q) (meaningNeg73 q) (meaning903 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 73 = true ∨ valuation q 903 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 904 = true := by
  have hs : count904 q = (countLit q [-70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (902)) (literal (valuationOf q) (904)) (countLit q [-70]) (countLit q [-71, -73]) (count904 q) 1 (meaning902 q) (meaning904 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 904 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 903 = false ∨ valuationOf q 905 = true := by
  have hs : count904 q = (countLit q [-70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (903)) (literal (valuationOf q) (905)) (countLit q [-70]) (countLit q [-71, -73]) (count904 q) 2 (meaning903 q) (meaning905 q) hs
  change valuationOf q 903 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 903 = false ∨ valuation q 905 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 904 = true := by
  have hs : count904 q = (countLit q [-70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71, -73])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (904)) (countLit q [-70]) (countLit q [-71, -73]) (count904 q) 1 (meaningNeg70 q) (meaning904 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 904 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 902 = false ∨ valuationOf q 905 = true := by
  have hs : count904 q = (countLit q [-70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (902)) (literal (valuationOf q) (905)) (countLit q [-70]) (countLit q [-71, -73]) (count904 q) 1 1 (meaningNeg70 q) (meaning902 q) (meaning905 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 902 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 902 = false ∨ valuation q 905 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 907 = true := by
  have hs : count907 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (907)) (countLit q [-76]) (countLit q [-77]) (count907 q) 1 (meaningNeg77 q) (meaning907 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 907 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 907 = true := by
  have hs : count907 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (907)) (countLit q [-76]) (countLit q [-77]) (count907 q) 1 (meaningNeg76 q) (meaning907 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 907 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 77 = true ∨ valuationOf q 908 = true := by
  have hs : count907 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (908)) (countLit q [-76]) (countLit q [-77]) (count907 q) 1 1 (meaningNeg76 q) (meaningNeg77 q) (meaning908 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 77 = true ∨ valuation q 908 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 909 = true := by
  have hs : count909 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (909)) (countLit q [-79]) (countLit q [-80]) (count909 q) 1 (meaningNeg80 q) (meaning909 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 909 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 80 = true ∨ valuationOf q 910 = true := by
  have hs : count909 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (910)) (countLit q [-79]) (countLit q [-80]) (count909 q) 1 1 (meaningNeg79 q) (meaningNeg80 q) (meaning910 q) hs
  change (! (valuationOf q 79)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 80 = true ∨ valuation q 910 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 912 = true := by
  have hs : count911 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_right (literal (valuationOf q) (910)) (literal (valuationOf q) (912)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count911 q) 2 (meaning910 q) (meaning912 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 912 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 909 = false ∨ valuationOf q 912 = true := by
  have hs : count911 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (909)) (literal (valuationOf q) (912)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count911 q) 1 1 (meaning907 q) (meaning909 q) (meaning912 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 909 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 909 = false ∨ valuation q 912 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 910 = false ∨ valuationOf q 913 = true := by
  have hs : count911 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (910)) (literal (valuationOf q) (913)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count911 q) 1 2 (meaning907 q) (meaning910 q) (meaning913 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 910 = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 910 = false ∨ valuation q 913 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 909 = false ∨ valuationOf q 913 = true := by
  have hs : count911 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (909)) (literal (valuationOf q) (913)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count911 q) 2 1 (meaning908 q) (meaning909 q) (meaning913 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 909 = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 909 = false ∨ valuation q 913 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 910 = false ∨ valuationOf q 914 = true := by
  have hs : count911 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (910)) (literal (valuationOf q) (914)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count911 q) 2 2 (meaning908 q) (meaning910 q) (meaning914 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 910 = false ∨ valuationOf q 914 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 910 = false ∨ valuation q 914 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 916 = true := by
  have hs : count915 q = (countLit q [-70, -71, -73]) + (countLit q [-76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-70, -71, -73]) (l₂ := [-76, -77, -79, -80])
  have hm := merge_right (literal (valuationOf q) (912)) (literal (valuationOf q) (916)) (countLit q [-70, -71, -73]) (countLit q [-76, -77, -79, -80]) (count915 q) 2 (meaning912 q) (meaning916 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 916 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 913 = false ∨ valuationOf q 917 = true := by
  have hs : count915 q = (countLit q [-70, -71, -73]) + (countLit q [-76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-70, -71, -73]) (l₂ := [-76, -77, -79, -80])
  have hm := merge_right (literal (valuationOf q) (913)) (literal (valuationOf q) (917)) (countLit q [-70, -71, -73]) (countLit q [-76, -77, -79, -80]) (count915 q) 3 (meaning913 q) (meaning917 q) hs
  change valuationOf q 913 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 913 = false ∨ valuation q 917 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 918 = true := by
  have hs : count915 q = (countLit q [-70, -71, -73]) + (countLit q [-76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-70, -71, -73]) (l₂ := [-76, -77, -79, -80])
  have hm := merge_right (literal (valuationOf q) (914)) (literal (valuationOf q) (918)) (countLit q [-70, -71, -73]) (countLit q [-76, -77, -79, -80]) (count915 q) 4 (meaning914 q) (meaning918 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 918 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 904 = false ∨ valuationOf q 912 = false ∨ valuationOf q 917 = true := by
  have hs : count915 q = (countLit q [-70, -71, -73]) + (countLit q [-76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-70, -71, -73]) (l₂ := [-76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (904)) (literal (valuationOf q) (912)) (literal (valuationOf q) (917)) (countLit q [-70, -71, -73]) (countLit q [-76, -77, -79, -80]) (count915 q) 1 2 (meaning904 q) (meaning912 q) (meaning917 q) hs
  change valuationOf q 904 = false ∨ valuationOf q 912 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 904 = false ∨ valuation q 912 = false ∨ valuation q 917 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 904 = false ∨ valuationOf q 913 = false ∨ valuationOf q 918 = true := by
  have hs : count915 q = (countLit q [-70, -71, -73]) + (countLit q [-76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-70, -71, -73]) (l₂ := [-76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (904)) (literal (valuationOf q) (913)) (literal (valuationOf q) (918)) (countLit q [-70, -71, -73]) (countLit q [-76, -77, -79, -80]) (count915 q) 1 3 (meaning904 q) (meaning913 q) (meaning918 q) hs
  change valuationOf q 904 = false ∨ valuationOf q 913 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 904 = false ∨ valuation q 913 = false ∨ valuation q 918 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 904 = false ∨ valuationOf q 914 = false ∨ valuationOf q 919 = true := by
  have hs : count915 q = (countLit q [-70, -71, -73]) + (countLit q [-76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-70, -71, -73]) (l₂ := [-76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (904)) (literal (valuationOf q) (914)) (literal (valuationOf q) (919)) (countLit q [-70, -71, -73]) (countLit q [-76, -77, -79, -80]) (count915 q) 1 4 (meaning904 q) (meaning914 q) (meaning919 q) hs
  change valuationOf q 904 = false ∨ valuationOf q 914 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 904 = false ∨ valuation q 914 = false ∨ valuation q 919 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 905 = false ∨ valuationOf q 912 = false ∨ valuationOf q 918 = true := by
  have hs : count915 q = (countLit q [-70, -71, -73]) + (countLit q [-76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-70, -71, -73]) (l₂ := [-76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (905)) (literal (valuationOf q) (912)) (literal (valuationOf q) (918)) (countLit q [-70, -71, -73]) (countLit q [-76, -77, -79, -80]) (count915 q) 2 2 (meaning905 q) (meaning912 q) (meaning918 q) hs
  change valuationOf q 905 = false ∨ valuationOf q 912 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 905 = false ∨ valuation q 912 = false ∨ valuation q 918 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 905 = false ∨ valuationOf q 913 = false ∨ valuationOf q 919 = true := by
  have hs : count915 q = (countLit q [-70, -71, -73]) + (countLit q [-76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-70, -71, -73]) (l₂ := [-76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (905)) (literal (valuationOf q) (913)) (literal (valuationOf q) (919)) (countLit q [-70, -71, -73]) (countLit q [-76, -77, -79, -80]) (count915 q) 2 3 (meaning905 q) (meaning913 q) (meaning919 q) hs
  change valuationOf q 905 = false ∨ valuationOf q 913 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 905 = false ∨ valuation q 913 = false ∨ valuation q 919 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 905 = false ∨ valuationOf q 914 = false ∨ valuationOf q 920 = true := by
  have hs : count915 q = (countLit q [-70, -71, -73]) + (countLit q [-76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-70, -71, -73]) (l₂ := [-76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (905)) (literal (valuationOf q) (914)) (literal (valuationOf q) (920)) (countLit q [-70, -71, -73]) (countLit q [-76, -77, -79, -80]) (count915 q) 2 4 (meaning905 q) (meaning914 q) (meaning920 q) hs
  change valuationOf q 905 = false ∨ valuationOf q 914 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 905 = false ∨ valuation q 914 = false ∨ valuation q 920 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 923 = true := by
  have hs : count922 q = (countLit q [-55, -57, -60, -62, -63, -65, -68]) + (countLit q [-70, -71, -73, -76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68]) (l₂ := [-70, -71, -73, -76, -77, -79, -80])
  have hm := merge_right (literal (valuationOf q) (916)) (literal (valuationOf q) (923)) (countLit q [-55, -57, -60, -62, -63, -65, -68]) (countLit q [-70, -71, -73, -76, -77, -79, -80]) (count922 q) 2 (meaning916 q) (meaning923 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 923 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 924 = true := by
  have hs : count922 q = (countLit q [-55, -57, -60, -62, -63, -65, -68]) + (countLit q [-70, -71, -73, -76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68]) (l₂ := [-70, -71, -73, -76, -77, -79, -80])
  have hm := merge_right (literal (valuationOf q) (917)) (literal (valuationOf q) (924)) (countLit q [-55, -57, -60, -62, -63, -65, -68]) (countLit q [-70, -71, -73, -76, -77, -79, -80]) (count922 q) 3 (meaning917 q) (meaning924 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 924 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 925 = true := by
  have hs : count922 q = (countLit q [-55, -57, -60, -62, -63, -65, -68]) + (countLit q [-70, -71, -73, -76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68]) (l₂ := [-70, -71, -73, -76, -77, -79, -80])
  have hm := merge_right (literal (valuationOf q) (918)) (literal (valuationOf q) (925)) (countLit q [-55, -57, -60, -62, -63, -65, -68]) (countLit q [-70, -71, -73, -76, -77, -79, -80]) (count922 q) 4 (meaning918 q) (meaning925 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 925 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 927 = true := by
  have hs : count922 q = (countLit q [-55, -57, -60, -62, -63, -65, -68]) + (countLit q [-70, -71, -73, -76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68]) (l₂ := [-70, -71, -73, -76, -77, -79, -80])
  have hm := merge_right (literal (valuationOf q) (920)) (literal (valuationOf q) (927)) (countLit q [-55, -57, -60, -62, -63, -65, -68]) (countLit q [-70, -71, -73, -76, -77, -79, -80]) (count922 q) 6 (meaning920 q) (meaning927 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 927 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 916 = false ∨ valuationOf q 924 = true := by
  have hs : count922 q = (countLit q [-55, -57, -60, -62, -63, -65, -68]) + (countLit q [-70, -71, -73, -76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68]) (l₂ := [-70, -71, -73, -76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (916)) (literal (valuationOf q) (924)) (countLit q [-55, -57, -60, -62, -63, -65, -68]) (countLit q [-70, -71, -73, -76, -77, -79, -80]) (count922 q) 1 2 (meaning895 q) (meaning916 q) (meaning924 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 916 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 916 = false ∨ valuation q 924 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 917 = false ∨ valuationOf q 925 = true := by
  have hs : count922 q = (countLit q [-55, -57, -60, -62, -63, -65, -68]) + (countLit q [-70, -71, -73, -76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68]) (l₂ := [-70, -71, -73, -76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (917)) (literal (valuationOf q) (925)) (countLit q [-55, -57, -60, -62, -63, -65, -68]) (countLit q [-70, -71, -73, -76, -77, -79, -80]) (count922 q) 1 3 (meaning895 q) (meaning917 q) (meaning925 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 917 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 917 = false ∨ valuation q 925 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 918 = false ∨ valuationOf q 926 = true := by
  have hs : count922 q = (countLit q [-55, -57, -60, -62, -63, -65, -68]) + (countLit q [-70, -71, -73, -76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68]) (l₂ := [-70, -71, -73, -76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (918)) (literal (valuationOf q) (926)) (countLit q [-55, -57, -60, -62, -63, -65, -68]) (countLit q [-70, -71, -73, -76, -77, -79, -80]) (count922 q) 1 4 (meaning895 q) (meaning918 q) (meaning926 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 918 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 918 = false ∨ valuation q 926 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E123.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112123
