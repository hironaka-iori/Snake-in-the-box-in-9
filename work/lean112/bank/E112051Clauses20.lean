import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 913 = false ∨ valuationOf q 916 = true := by
  have hs : count915 q = (countLit q [-64, -65]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-64, -65]) (l₂ := [-67, -70])
  have hm := merge_two (literal (valuationOf q) (911)) (literal (valuationOf q) (913)) (literal (valuationOf q) (916)) (countLit q [-64, -65]) (countLit q [-67, -70]) (count915 q) 1 1 (meaning911 q) (meaning913 q) (meaning916 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 913 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 913 = false ∨ valuation q 916 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 914 = false ∨ valuationOf q 917 = true := by
  have hs : count915 q = (countLit q [-64, -65]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-64, -65]) (l₂ := [-67, -70])
  have hm := merge_two (literal (valuationOf q) (911)) (literal (valuationOf q) (914)) (literal (valuationOf q) (917)) (countLit q [-64, -65]) (countLit q [-67, -70]) (count915 q) 1 2 (meaning911 q) (meaning914 q) (meaning917 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 914 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 914 = false ∨ valuation q 917 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 916 = true := by
  have hs : count915 q = (countLit q [-64, -65]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-64, -65]) (l₂ := [-67, -70])
  have hm := merge_left (literal (valuationOf q) (912)) (literal (valuationOf q) (916)) (countLit q [-64, -65]) (countLit q [-67, -70]) (count915 q) 2 (meaning912 q) (meaning916 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 916 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 913 = false ∨ valuationOf q 917 = true := by
  have hs : count915 q = (countLit q [-64, -65]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-64, -65]) (l₂ := [-67, -70])
  have hm := merge_two (literal (valuationOf q) (912)) (literal (valuationOf q) (913)) (literal (valuationOf q) (917)) (countLit q [-64, -65]) (countLit q [-67, -70]) (count915 q) 2 1 (meaning912 q) (meaning913 q) (meaning917 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 913 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 913 = false ∨ valuation q 917 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 915 = false ∨ valuationOf q 919 = true := by
  have hs : count919 q = (countLit q [-57, -58, -59]) + (countLit q [-64, -65, -67, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59]) (l₂ := [-64, -65, -67, -70])
  have hm := merge_right (literal (valuationOf q) (915)) (literal (valuationOf q) (919)) (countLit q [-57, -58, -59]) (countLit q [-64, -65, -67, -70]) (count919 q) 1 (meaning915 q) (meaning919 q) hs
  change valuationOf q 915 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 915 = false ∨ valuation q 919 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 920 = true := by
  have hs : count919 q = (countLit q [-57, -58, -59]) + (countLit q [-64, -65, -67, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59]) (l₂ := [-64, -65, -67, -70])
  have hm := merge_right (literal (valuationOf q) (916)) (literal (valuationOf q) (920)) (countLit q [-57, -58, -59]) (countLit q [-64, -65, -67, -70]) (count919 q) 2 (meaning916 q) (meaning920 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 920 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 921 = true := by
  have hs : count919 q = (countLit q [-57, -58, -59]) + (countLit q [-64, -65, -67, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59]) (l₂ := [-64, -65, -67, -70])
  have hm := merge_right (literal (valuationOf q) (917)) (literal (valuationOf q) (921)) (countLit q [-57, -58, -59]) (countLit q [-64, -65, -67, -70]) (count919 q) 3 (meaning917 q) (meaning921 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 921 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 919 = true := by
  have hs : count919 q = (countLit q [-57, -58, -59]) + (countLit q [-64, -65, -67, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59]) (l₂ := [-64, -65, -67, -70])
  have hm := merge_left (literal (valuationOf q) (908)) (literal (valuationOf q) (919)) (countLit q [-57, -58, -59]) (countLit q [-64, -65, -67, -70]) (count919 q) 1 (meaning908 q) (meaning919 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 919 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 915 = false ∨ valuationOf q 920 = true := by
  have hs : count919 q = (countLit q [-57, -58, -59]) + (countLit q [-64, -65, -67, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59]) (l₂ := [-64, -65, -67, -70])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (915)) (literal (valuationOf q) (920)) (countLit q [-57, -58, -59]) (countLit q [-64, -65, -67, -70]) (count919 q) 1 1 (meaning908 q) (meaning915 q) (meaning920 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 915 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 915 = false ∨ valuation q 920 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 916 = false ∨ valuationOf q 921 = true := by
  have hs : count919 q = (countLit q [-57, -58, -59]) + (countLit q [-64, -65, -67, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59]) (l₂ := [-64, -65, -67, -70])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (916)) (literal (valuationOf q) (921)) (countLit q [-57, -58, -59]) (countLit q [-64, -65, -67, -70]) (count919 q) 1 2 (meaning908 q) (meaning916 q) (meaning921 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 916 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 916 = false ∨ valuation q 921 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 917 = false ∨ valuationOf q 922 = true := by
  have hs : count919 q = (countLit q [-57, -58, -59]) + (countLit q [-64, -65, -67, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59]) (l₂ := [-64, -65, -67, -70])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (917)) (literal (valuationOf q) (922)) (countLit q [-57, -58, -59]) (countLit q [-64, -65, -67, -70]) (count919 q) 1 3 (meaning908 q) (meaning917 q) (meaning922 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 917 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 917 = false ∨ valuation q 922 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 920 = true := by
  have hs : count919 q = (countLit q [-57, -58, -59]) + (countLit q [-64, -65, -67, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59]) (l₂ := [-64, -65, -67, -70])
  have hm := merge_left (literal (valuationOf q) (909)) (literal (valuationOf q) (920)) (countLit q [-57, -58, -59]) (countLit q [-64, -65, -67, -70]) (count919 q) 2 (meaning909 q) (meaning920 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 920 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 915 = false ∨ valuationOf q 921 = true := by
  have hs : count919 q = (countLit q [-57, -58, -59]) + (countLit q [-64, -65, -67, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59]) (l₂ := [-64, -65, -67, -70])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (915)) (literal (valuationOf q) (921)) (countLit q [-57, -58, -59]) (countLit q [-64, -65, -67, -70]) (count919 q) 2 1 (meaning909 q) (meaning915 q) (meaning921 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 915 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 915 = false ∨ valuation q 921 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 916 = false ∨ valuationOf q 922 = true := by
  have hs : count919 q = (countLit q [-57, -58, -59]) + (countLit q [-64, -65, -67, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59]) (l₂ := [-64, -65, -67, -70])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (916)) (literal (valuationOf q) (922)) (countLit q [-57, -58, -59]) (countLit q [-64, -65, -67, -70]) (count919 q) 2 2 (meaning909 q) (meaning916 q) (meaning922 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 916 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 916 = false ∨ valuation q 922 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 917 = false ∨ valuationOf q 923 = true := by
  have hs : count919 q = (countLit q [-57, -58, -59]) + (countLit q [-64, -65, -67, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59]) (l₂ := [-64, -65, -67, -70])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (917)) (literal (valuationOf q) (923)) (countLit q [-57, -58, -59]) (countLit q [-64, -65, -67, -70]) (count919 q) 2 3 (meaning909 q) (meaning917 q) (meaning923 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 917 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 917 = false ∨ valuation q 923 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 915 = false ∨ valuationOf q 922 = true := by
  have hs : count919 q = (countLit q [-57, -58, -59]) + (countLit q [-64, -65, -67, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59]) (l₂ := [-64, -65, -67, -70])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (915)) (literal (valuationOf q) (922)) (countLit q [-57, -58, -59]) (countLit q [-64, -65, -67, -70]) (count919 q) 3 1 (meaning910 q) (meaning915 q) (meaning922 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 915 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 915 = false ∨ valuation q 922 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 916 = false ∨ valuationOf q 923 = true := by
  have hs : count919 q = (countLit q [-57, -58, -59]) + (countLit q [-64, -65, -67, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59]) (l₂ := [-64, -65, -67, -70])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (916)) (literal (valuationOf q) (923)) (countLit q [-57, -58, -59]) (countLit q [-64, -65, -67, -70]) (count919 q) 3 2 (meaning910 q) (meaning916 q) (meaning923 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 916 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 916 = false ∨ valuation q 923 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 926 = true := by
  have hs : count926 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (926)) (countLit q [-73]) (countLit q [-74]) (count926 q) 1 (meaningNeg74 q) (meaning926 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 926 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 926 = true := by
  have hs : count926 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (926)) (countLit q [-73]) (countLit q [-74]) (count926 q) 1 (meaningNeg73 q) (meaning926 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 926 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 74 = true ∨ valuationOf q 927 = true := by
  have hs : count926 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-73)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (927)) (countLit q [-73]) (countLit q [-74]) (count926 q) 1 1 (meaningNeg73 q) (meaningNeg74 q) (meaning927 q) hs
  change (! (valuationOf q 73)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 74 = true ∨ valuation q 927 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 928 = true := by
  have hs : count928 q = (countLit q [-72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -74])
  have hm := merge_right (literal (valuationOf q) (926)) (literal (valuationOf q) (928)) (countLit q [-72]) (countLit q [-73, -74]) (count928 q) 1 (meaning926 q) (meaning928 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 928 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 927 = false ∨ valuationOf q 929 = true := by
  have hs : count928 q = (countLit q [-72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -74])
  have hm := merge_right (literal (valuationOf q) (927)) (literal (valuationOf q) (929)) (countLit q [-72]) (countLit q [-73, -74]) (count928 q) 2 (meaning927 q) (meaning929 q) hs
  change valuationOf q 927 = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 927 = false ∨ valuation q 929 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 928 = true := by
  have hs : count928 q = (countLit q [-72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -74])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (928)) (countLit q [-72]) (countLit q [-73, -74]) (count928 q) 1 (meaningNeg72 q) (meaning928 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 928 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 926 = false ∨ valuationOf q 929 = true := by
  have hs : count928 q = (countLit q [-72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -74])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (926)) (literal (valuationOf q) (929)) (countLit q [-72]) (countLit q [-73, -74]) (count928 q) 1 1 (meaningNeg72 q) (meaning926 q) (meaning929 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 926 = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 926 = false ∨ valuation q 929 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 927 = false ∨ valuationOf q 930 = true := by
  have hs : count928 q = (countLit q [-72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73, -74])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (927)) (literal (valuationOf q) (930)) (countLit q [-72]) (countLit q [-73, -74]) (count928 q) 1 2 (meaningNeg72 q) (meaning927 q) (meaning930 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 927 = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 927 = false ∨ valuation q 930 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 931 = true := by
  have hs : count931 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (931)) (countLit q [-76]) (countLit q [-78]) (count931 q) 1 (meaningNeg78 q) (meaning931 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 931 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 931 = true := by
  have hs : count931 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (931)) (countLit q [-76]) (countLit q [-78]) (count931 q) 1 (meaningNeg76 q) (meaning931 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 931 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 78 = true ∨ valuationOf q 932 = true := by
  have hs : count931 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-78)) (literal (valuationOf q) (932)) (countLit q [-76]) (countLit q [-78]) (count931 q) 1 1 (meaningNeg76 q) (meaningNeg78 q) (meaning932 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 78)) = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 932 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 933 = true := by
  have hs : count933 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (933)) (countLit q [-80]) (countLit q [-81]) (count933 q) 1 (meaningNeg81 q) (meaning933 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 933 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 933 = true := by
  have hs : count933 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (933)) (countLit q [-80]) (countLit q [-81]) (count933 q) 1 (meaningNeg80 q) (meaning933 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 933 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 81 = true ∨ valuationOf q 934 = true := by
  have hs : count933 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (934)) (countLit q [-80]) (countLit q [-81]) (count933 q) 1 1 (meaningNeg80 q) (meaningNeg81 q) (meaning934 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 934 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 935 = true := by
  have hs : count935 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_right (literal (valuationOf q) (933)) (literal (valuationOf q) (935)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count935 q) 1 (meaning933 q) (meaning935 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 935 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E051.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112051
