import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 920 = true := by
  have hs : count920 q = (countLit q [-102]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (920)) (countLit q [-102]) (countLit q [-105]) (count920 q) 1 (meaningNeg105 q) (meaning920 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 920 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 920 = true := by
  have hs : count920 q = (countLit q [-102]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (920)) (countLit q [-102]) (countLit q [-105]) (count920 q) 1 (meaningNeg102 q) (meaning920 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 920 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 105 = true ∨ valuationOf q 921 = true := by
  have hs : count920 q = (countLit q [-102]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-102)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (921)) (countLit q [-102]) (countLit q [-105]) (count920 q) 1 1 (meaningNeg102 q) (meaningNeg105 q) (meaning921 q) hs
  change (! (valuationOf q 102)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 921 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 922 = true := by
  have hs : count922 q = (countLit q [-100, -101]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -105])
  have hm := merge_right (literal (valuationOf q) (920)) (literal (valuationOf q) (922)) (countLit q [-100, -101]) (countLit q [-102, -105]) (count922 q) 1 (meaning920 q) (meaning922 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 922 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 922 = true := by
  have hs : count922 q = (countLit q [-100, -101]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -105])
  have hm := merge_left (literal (valuationOf q) (918)) (literal (valuationOf q) (922)) (countLit q [-100, -101]) (countLit q [-102, -105]) (count922 q) 1 (meaning918 q) (meaning922 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 922 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 920 = false ∨ valuationOf q 923 = true := by
  have hs : count922 q = (countLit q [-100, -101]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -105])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (920)) (literal (valuationOf q) (923)) (countLit q [-100, -101]) (countLit q [-102, -105]) (count922 q) 1 1 (meaning918 q) (meaning920 q) (meaning923 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 920 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 920 = false ∨ valuation q 923 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 923 = true := by
  have hs : count922 q = (countLit q [-100, -101]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -105])
  have hm := merge_left (literal (valuationOf q) (919)) (literal (valuationOf q) (923)) (countLit q [-100, -101]) (countLit q [-102, -105]) (count922 q) 2 (meaning919 q) (meaning923 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 923 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 920 = false ∨ valuationOf q 924 = true := by
  have hs : count922 q = (countLit q [-100, -101]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -105])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (920)) (literal (valuationOf q) (924)) (countLit q [-100, -101]) (countLit q [-102, -105]) (count922 q) 2 1 (meaning919 q) (meaning920 q) (meaning924 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 920 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 920 = false ∨ valuation q 924 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 921 = false ∨ valuationOf q 925 = true := by
  have hs : count922 q = (countLit q [-100, -101]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -105])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (921)) (literal (valuationOf q) (925)) (countLit q [-100, -101]) (countLit q [-102, -105]) (count922 q) 2 2 (meaning919 q) (meaning921 q) (meaning925 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 921 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 921 = false ∨ valuation q 925 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 927 = true := by
  have hs : count926 q = (countLit q [-96, -97, -98]) + (countLit q [-100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -98]) (l₂ := [-100, -101, -102, -105])
  have hm := merge_left (literal (valuationOf q) (916)) (literal (valuationOf q) (927)) (countLit q [-96, -97, -98]) (countLit q [-100, -101, -102, -105]) (count926 q) 2 (meaning916 q) (meaning927 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 927 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 922 = false ∨ valuationOf q 928 = true := by
  have hs : count926 q = (countLit q [-96, -97, -98]) + (countLit q [-100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -98]) (l₂ := [-100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (922)) (literal (valuationOf q) (928)) (countLit q [-96, -97, -98]) (countLit q [-100, -101, -102, -105]) (count926 q) 2 1 (meaning916 q) (meaning922 q) (meaning928 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 922 = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 922 = false ∨ valuation q 928 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 923 = false ∨ valuationOf q 929 = true := by
  have hs : count926 q = (countLit q [-96, -97, -98]) + (countLit q [-100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -98]) (l₂ := [-100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (923)) (literal (valuationOf q) (929)) (countLit q [-96, -97, -98]) (countLit q [-100, -101, -102, -105]) (count926 q) 2 2 (meaning916 q) (meaning923 q) (meaning929 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 923 = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 923 = false ∨ valuation q 929 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 924 = false ∨ valuationOf q 930 = true := by
  have hs : count926 q = (countLit q [-96, -97, -98]) + (countLit q [-100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -98]) (l₂ := [-100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (924)) (literal (valuationOf q) (930)) (countLit q [-96, -97, -98]) (countLit q [-100, -101, -102, -105]) (count926 q) 2 3 (meaning916 q) (meaning924 q) (meaning930 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 924 = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 924 = false ∨ valuation q 930 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 925 = false ∨ valuationOf q 931 = true := by
  have hs : count926 q = (countLit q [-96, -97, -98]) + (countLit q [-100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -98]) (l₂ := [-100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (916)) (literal (valuationOf q) (925)) (literal (valuationOf q) (931)) (countLit q [-96, -97, -98]) (countLit q [-100, -101, -102, -105]) (count926 q) 2 4 (meaning916 q) (meaning925 q) (meaning931 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 925 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 925 = false ∨ valuation q 931 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 928 = true := by
  have hs : count926 q = (countLit q [-96, -97, -98]) + (countLit q [-100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -98]) (l₂ := [-100, -101, -102, -105])
  have hm := merge_left (literal (valuationOf q) (917)) (literal (valuationOf q) (928)) (countLit q [-96, -97, -98]) (countLit q [-100, -101, -102, -105]) (count926 q) 3 (meaning917 q) (meaning928 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 928 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 922 = false ∨ valuationOf q 929 = true := by
  have hs : count926 q = (countLit q [-96, -97, -98]) + (countLit q [-100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -98]) (l₂ := [-100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (922)) (literal (valuationOf q) (929)) (countLit q [-96, -97, -98]) (countLit q [-100, -101, -102, -105]) (count926 q) 3 1 (meaning917 q) (meaning922 q) (meaning929 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 922 = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 922 = false ∨ valuation q 929 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 917 = false ∨ valuationOf q 923 = false ∨ valuationOf q 930 = true := by
  have hs : count926 q = (countLit q [-96, -97, -98]) + (countLit q [-100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-96, -97, -98]) (l₂ := [-100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (917)) (literal (valuationOf q) (923)) (literal (valuationOf q) (930)) (countLit q [-96, -97, -98]) (countLit q [-100, -101, -102, -105]) (count926 q) 3 2 (meaning917 q) (meaning923 q) (meaning930 q) hs
  change valuationOf q 917 = false ∨ valuationOf q 923 = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 917 = false ∨ valuation q 923 = false ∨ valuation q 930 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 928 = false ∨ valuationOf q 936 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (928)) (literal (valuationOf q) (936)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 1 3 (meaning906 q) (meaning928 q) (meaning936 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 928 = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 928 = false ∨ valuation q 936 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 929 = false ∨ valuationOf q 937 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (929)) (literal (valuationOf q) (937)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 1 4 (meaning906 q) (meaning929 q) (meaning937 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 929 = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 929 = false ∨ valuation q 937 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 930 = false ∨ valuationOf q 938 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (930)) (literal (valuationOf q) (938)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 1 5 (meaning906 q) (meaning930 q) (meaning938 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 930 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 930 = false ∨ valuation q 938 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 927 = false ∨ valuationOf q 936 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (927)) (literal (valuationOf q) (936)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 2 2 (meaning907 q) (meaning927 q) (meaning936 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 927 = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 927 = false ∨ valuation q 936 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 928 = false ∨ valuationOf q 937 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (928)) (literal (valuationOf q) (937)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 2 3 (meaning907 q) (meaning928 q) (meaning937 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 928 = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 928 = false ∨ valuation q 937 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 929 = false ∨ valuationOf q 938 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (929)) (literal (valuationOf q) (938)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 2 4 (meaning907 q) (meaning929 q) (meaning938 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 929 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 929 = false ∨ valuation q 938 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 930 = false ∨ valuationOf q 939 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (930)) (literal (valuationOf q) (939)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 2 5 (meaning907 q) (meaning930 q) (meaning939 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 930 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 930 = false ∨ valuation q 939 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 927 = false ∨ valuationOf q 937 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (927)) (literal (valuationOf q) (937)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 3 2 (meaning908 q) (meaning927 q) (meaning937 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 927 = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 927 = false ∨ valuation q 937 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 928 = false ∨ valuationOf q 938 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (928)) (literal (valuationOf q) (938)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 3 3 (meaning908 q) (meaning928 q) (meaning938 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 928 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 928 = false ∨ valuation q 938 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 929 = false ∨ valuationOf q 939 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (929)) (literal (valuationOf q) (939)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 3 4 (meaning908 q) (meaning929 q) (meaning939 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 929 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 929 = false ∨ valuation q 939 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 930 = false ∨ valuationOf q 940 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (930)) (literal (valuationOf q) (940)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 3 5 (meaning908 q) (meaning930 q) (meaning940 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 930 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 930 = false ∨ valuation q 940 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 931 = false ∨ valuationOf q 941 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (931)) (literal (valuationOf q) (941)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 3 6 (meaning908 q) (meaning931 q) (meaning941 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 931 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 931 = false ∨ valuation q 941 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 927 = false ∨ valuationOf q 938 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (927)) (literal (valuationOf q) (938)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 4 2 (meaning909 q) (meaning927 q) (meaning938 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 927 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 927 = false ∨ valuation q 938 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 928 = false ∨ valuationOf q 939 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (928)) (literal (valuationOf q) (939)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 4 3 (meaning909 q) (meaning928 q) (meaning939 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 928 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 928 = false ∨ valuation q 939 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 929 = false ∨ valuationOf q 940 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (929)) (literal (valuationOf q) (940)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 4 4 (meaning909 q) (meaning929 q) (meaning940 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 929 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 929 = false ∨ valuation q 940 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E151.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112151
