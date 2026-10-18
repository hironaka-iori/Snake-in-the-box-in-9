import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 930 = false ∨ valuationOf q 941 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (930)) (literal (valuationOf q) (941)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 4 5 (meaning909 q) (meaning930 q) (meaning941 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 930 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 930 = false ∨ valuation q 941 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 927 = false ∨ valuationOf q 939 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (927)) (literal (valuationOf q) (939)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 5 2 (meaning910 q) (meaning927 q) (meaning939 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 927 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 927 = false ∨ valuation q 939 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 910 = false ∨ valuationOf q 928 = false ∨ valuationOf q 940 = true := by
  have hs : count933 q = (countLit q [-80, -83, -87, -89, -90, -92, -93]) + (countLit q [-96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -83, -87, -89, -90, -92, -93]) (l₂ := [-96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (910)) (literal (valuationOf q) (928)) (literal (valuationOf q) (940)) (countLit q [-80, -83, -87, -89, -90, -92, -93]) (countLit q [-96, -97, -98, -100, -101, -102, -105]) (count933 q) 5 3 (meaning910 q) (meaning928 q) (meaning940 q) hs
  change valuationOf q 910 = false ∨ valuationOf q 928 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 910 = false ∨ valuation q 928 = false ∨ valuation q 940 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 937 = false ∨ valuationOf q 952 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (937)) (literal (valuationOf q) (952)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 1 5 (meaning880 q) (meaning937 q) (meaning952 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 937 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 937 = false ∨ valuation q 952 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 941 = false ∨ valuationOf q 956 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (941)) (literal (valuationOf q) (956)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 1 9 (meaning880 q) (meaning941 q) (meaning956 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 941 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 941 = false ∨ valuation q 956 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 937 = false ∨ valuationOf q 953 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (937)) (literal (valuationOf q) (953)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 2 5 (meaning881 q) (meaning937 q) (meaning953 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 937 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 937 = false ∨ valuation q 953 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 938 = false ∨ valuationOf q 954 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (938)) (literal (valuationOf q) (954)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 2 6 (meaning881 q) (meaning938 q) (meaning954 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 938 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 938 = false ∨ valuation q 954 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 939 = false ∨ valuationOf q 955 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (939)) (literal (valuationOf q) (955)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 2 7 (meaning881 q) (meaning939 q) (meaning955 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 939 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 939 = false ∨ valuation q 955 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 940 = false ∨ valuationOf q 956 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (940)) (literal (valuationOf q) (956)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 2 8 (meaning881 q) (meaning940 q) (meaning956 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 940 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 940 = false ∨ valuation q 956 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 936 = false ∨ valuationOf q 953 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (936)) (literal (valuationOf q) (953)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 3 4 (meaning882 q) (meaning936 q) (meaning953 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 936 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 936 = false ∨ valuation q 953 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 937 = false ∨ valuationOf q 954 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (937)) (literal (valuationOf q) (954)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 3 5 (meaning882 q) (meaning937 q) (meaning954 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 937 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 937 = false ∨ valuation q 954 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 938 = false ∨ valuationOf q 955 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (938)) (literal (valuationOf q) (955)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 3 6 (meaning882 q) (meaning938 q) (meaning955 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 938 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 938 = false ∨ valuation q 955 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 939 = false ∨ valuationOf q 956 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (939)) (literal (valuationOf q) (956)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 3 7 (meaning882 q) (meaning939 q) (meaning956 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 939 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 939 = false ∨ valuation q 956 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 936 = false ∨ valuationOf q 954 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (936)) (literal (valuationOf q) (954)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 4 4 (meaning883 q) (meaning936 q) (meaning954 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 936 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 936 = false ∨ valuation q 954 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 937 = false ∨ valuationOf q 955 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (937)) (literal (valuationOf q) (955)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 4 5 (meaning883 q) (meaning937 q) (meaning955 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 937 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 937 = false ∨ valuation q 955 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 938 = false ∨ valuationOf q 956 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (938)) (literal (valuationOf q) (956)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 4 6 (meaning883 q) (meaning938 q) (meaning956 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 938 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 938 = false ∨ valuation q 956 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 936 = false ∨ valuationOf q 955 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (936)) (literal (valuationOf q) (955)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 5 4 (meaning884 q) (meaning936 q) (meaning955 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 936 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 936 = false ∨ valuation q 955 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 937 = false ∨ valuationOf q 956 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (937)) (literal (valuationOf q) (956)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 5 5 (meaning884 q) (meaning937 q) (meaning956 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 937 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 937 = false ∨ valuation q 956 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 936 = false ∨ valuationOf q 956 = true := by
  have hs : count947 q = (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) + (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (l₂ := [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (885)) (literal (valuationOf q) (936)) (literal (valuationOf q) (956)) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]) (countLit q [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count947 q) 6 4 (meaning885 q) (meaning936 q) (meaning956 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 936 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 936 = false ∨ valuation q 956 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 833 = false ∨ valuationOf q 956 = false ∨ valuationOf q 974 = true := by
  have hs : count961 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) + (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (l₂ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (833)) (literal (valuationOf q) (956)) (literal (valuationOf q) (974)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count961 q) 4 10 (meaning833 q) (meaning956 q) (meaning974 q) hs
  change valuationOf q 833 = false ∨ valuationOf q 956 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 833 = false ∨ valuation q 956 = false ∨ valuation q 974 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 834 = false ∨ valuationOf q 955 = false ∨ valuationOf q 974 = true := by
  have hs : count961 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) + (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (l₂ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (834)) (literal (valuationOf q) (955)) (literal (valuationOf q) (974)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count961 q) 5 9 (meaning834 q) (meaning955 q) (meaning974 q) hs
  change valuationOf q 834 = false ∨ valuationOf q 955 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 834 = false ∨ valuation q 955 = false ∨ valuation q 974 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 835 = false ∨ valuationOf q 954 = false ∨ valuationOf q 974 = true := by
  have hs : count961 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) + (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (l₂ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (835)) (literal (valuationOf q) (954)) (literal (valuationOf q) (974)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count961 q) 6 8 (meaning835 q) (meaning954 q) (meaning974 q) hs
  change valuationOf q 835 = false ∨ valuationOf q 954 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 835 = false ∨ valuation q 954 = false ∨ valuation q 974 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 836 = false ∨ valuationOf q 953 = false ∨ valuationOf q 974 = true := by
  have hs : count961 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) + (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (l₂ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (836)) (literal (valuationOf q) (953)) (literal (valuationOf q) (974)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count961 q) 7 7 (meaning836 q) (meaning953 q) (meaning974 q) hs
  change valuationOf q 836 = false ∨ valuationOf q 953 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 836 = false ∨ valuation q 953 = false ∨ valuation q 974 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 952 = false ∨ valuationOf q 974 = true := by
  have hs : count961 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) + (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (l₂ := [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (952)) (literal (valuationOf q) (974)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (countLit q [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]) (count961 q) 8 6 (meaning837 q) (meaning952 q) (meaning974 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 952 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 952 = false ∨ valuation q 974 = true := counterClause568 (baseVal q)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 974 = false := by
  rw [value974]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count961 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 51 = false ∨ valuation q 56 = false := by
  rw [value3, value4, value51, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (18 : Vertex) (26 : Vertex) (274 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value14, value15, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (172 : Vertex) (173 : Vertex) (188 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 22 = false := by
  rw [value17, value18, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (178 : Vertex) (179 : Vertex) (186 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value33, value34, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (210 : Vertex) (211 : Vertex) (218 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 44 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value42, value44, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (262 : Vertex) (276 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value76, value78, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (422 : Vertex) (436 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value80, value81, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (425 : Vertex) (440 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E151.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112151
