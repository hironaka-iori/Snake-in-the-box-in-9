import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 919 = false ∨ valuationOf q 927 = true := by
  have hs : count922 q = (countLit q [-55, -57, -60, -62, -63, -65, -68]) + (countLit q [-70, -71, -73, -76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68]) (l₂ := [-70, -71, -73, -76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (919)) (literal (valuationOf q) (927)) (countLit q [-55, -57, -60, -62, -63, -65, -68]) (countLit q [-70, -71, -73, -76, -77, -79, -80]) (count922 q) 1 5 (meaning895 q) (meaning919 q) (meaning927 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 919 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 919 = false ∨ valuation q 927 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 920 = false ∨ valuationOf q 928 = true := by
  have hs : count922 q = (countLit q [-55, -57, -60, -62, -63, -65, -68]) + (countLit q [-70, -71, -73, -76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68]) (l₂ := [-70, -71, -73, -76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (920)) (literal (valuationOf q) (928)) (countLit q [-55, -57, -60, -62, -63, -65, -68]) (countLit q [-70, -71, -73, -76, -77, -79, -80]) (count922 q) 1 6 (meaning895 q) (meaning920 q) (meaning928 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 920 = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 920 = false ∨ valuation q 928 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 916 = false ∨ valuationOf q 925 = true := by
  have hs : count922 q = (countLit q [-55, -57, -60, -62, -63, -65, -68]) + (countLit q [-70, -71, -73, -76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68]) (l₂ := [-70, -71, -73, -76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (916)) (literal (valuationOf q) (925)) (countLit q [-55, -57, -60, -62, -63, -65, -68]) (countLit q [-70, -71, -73, -76, -77, -79, -80]) (count922 q) 2 2 (meaning896 q) (meaning916 q) (meaning925 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 916 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 916 = false ∨ valuation q 925 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 917 = false ∨ valuationOf q 926 = true := by
  have hs : count922 q = (countLit q [-55, -57, -60, -62, -63, -65, -68]) + (countLit q [-70, -71, -73, -76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68]) (l₂ := [-70, -71, -73, -76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (917)) (literal (valuationOf q) (926)) (countLit q [-55, -57, -60, -62, -63, -65, -68]) (countLit q [-70, -71, -73, -76, -77, -79, -80]) (count922 q) 2 3 (meaning896 q) (meaning917 q) (meaning926 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 917 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 917 = false ∨ valuation q 926 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 918 = false ∨ valuationOf q 927 = true := by
  have hs : count922 q = (countLit q [-55, -57, -60, -62, -63, -65, -68]) + (countLit q [-70, -71, -73, -76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68]) (l₂ := [-70, -71, -73, -76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (918)) (literal (valuationOf q) (927)) (countLit q [-55, -57, -60, -62, -63, -65, -68]) (countLit q [-70, -71, -73, -76, -77, -79, -80]) (count922 q) 2 4 (meaning896 q) (meaning918 q) (meaning927 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 918 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 918 = false ∨ valuation q 927 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 916 = false ∨ valuationOf q 926 = true := by
  have hs : count922 q = (countLit q [-55, -57, -60, -62, -63, -65, -68]) + (countLit q [-70, -71, -73, -76, -77, -79, -80]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60, -62, -63, -65, -68]) (l₂ := [-70, -71, -73, -76, -77, -79, -80])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (916)) (literal (valuationOf q) (926)) (countLit q [-55, -57, -60, -62, -63, -65, -68]) (countLit q [-70, -71, -73, -76, -77, -79, -80]) (count922 q) 3 2 (meaning897 q) (meaning916 q) (meaning926 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 916 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 916 = false ∨ valuation q 926 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 936 = true := by
  have hs : count936 q = (countLit q [-83]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (936)) (countLit q [-83]) (countLit q [-87]) (count936 q) 1 (meaningNeg83 q) (meaning936 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 936 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-81]) + (countLit q [-83, -87]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83, -87])
  have hm := merge_right (literal (valuationOf q) (936)) (literal (valuationOf q) (938)) (countLit q [-81]) (countLit q [-83, -87]) (count938 q) 1 (meaning936 q) (meaning938 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 938 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-81]) + (countLit q [-83, -87]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83, -87])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (938)) (countLit q [-81]) (countLit q [-83, -87]) (count938 q) 1 (meaningNeg81 q) (meaning938 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 938 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 936 = false ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-81]) + (countLit q [-83, -87]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83, -87])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (936)) (literal (valuationOf q) (939)) (countLit q [-81]) (countLit q [-83, -87]) (count938 q) 1 1 (meaningNeg81 q) (meaning936 q) (meaning939 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 936 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 936 = false ∨ valuation q 939 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 941 = true := by
  have hs : count941 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (941)) (countLit q [-88]) (countLit q [-90]) (count941 q) 1 (meaningNeg88 q) (meaning941 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 941 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 943 = true := by
  have hs : count943 q = (countLit q [-92]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (943)) (countLit q [-92]) (countLit q [-94]) (count943 q) 1 (meaningNeg92 q) (meaning943 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 943 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 945 = true := by
  have hs : count945 q = (countLit q [-88, -90]) + (countLit q [-92, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -90]) (l₂ := [-92, -94])
  have hm := merge_right (literal (valuationOf q) (943)) (literal (valuationOf q) (945)) (countLit q [-88, -90]) (countLit q [-92, -94]) (count945 q) 1 (meaning943 q) (meaning945 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 945 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 941 = false ∨ valuationOf q 943 = false ∨ valuationOf q 946 = true := by
  have hs : count945 q = (countLit q [-88, -90]) + (countLit q [-92, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -90]) (l₂ := [-92, -94])
  have hm := merge_two (literal (valuationOf q) (941)) (literal (valuationOf q) (943)) (literal (valuationOf q) (946)) (countLit q [-88, -90]) (countLit q [-92, -94]) (count945 q) 1 1 (meaning941 q) (meaning943 q) (meaning946 q) hs
  change valuationOf q 941 = false ∨ valuationOf q 943 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 941 = false ∨ valuation q 943 = false ∨ valuation q 946 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 949 = true := by
  have hs : count949 q = (countLit q [-81, -83, -87]) + (countLit q [-88, -90, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-81, -83, -87]) (l₂ := [-88, -90, -92, -94])
  have hm := merge_right (literal (valuationOf q) (945)) (literal (valuationOf q) (949)) (countLit q [-81, -83, -87]) (countLit q [-88, -90, -92, -94]) (count949 q) 1 (meaning945 q) (meaning949 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 949 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 950 = true := by
  have hs : count949 q = (countLit q [-81, -83, -87]) + (countLit q [-88, -90, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-81, -83, -87]) (l₂ := [-88, -90, -92, -94])
  have hm := merge_right (literal (valuationOf q) (946)) (literal (valuationOf q) (950)) (countLit q [-81, -83, -87]) (countLit q [-88, -90, -92, -94]) (count949 q) 2 (meaning946 q) (meaning950 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 950 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 945 = false ∨ valuationOf q 950 = true := by
  have hs : count949 q = (countLit q [-81, -83, -87]) + (countLit q [-88, -90, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-81, -83, -87]) (l₂ := [-88, -90, -92, -94])
  have hm := merge_two (literal (valuationOf q) (938)) (literal (valuationOf q) (945)) (literal (valuationOf q) (950)) (countLit q [-81, -83, -87]) (countLit q [-88, -90, -92, -94]) (count949 q) 1 1 (meaning938 q) (meaning945 q) (meaning950 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 945 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 945 = false ∨ valuation q 950 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 946 = false ∨ valuationOf q 951 = true := by
  have hs : count949 q = (countLit q [-81, -83, -87]) + (countLit q [-88, -90, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-81, -83, -87]) (l₂ := [-88, -90, -92, -94])
  have hm := merge_two (literal (valuationOf q) (938)) (literal (valuationOf q) (946)) (literal (valuationOf q) (951)) (countLit q [-81, -83, -87]) (countLit q [-88, -90, -92, -94]) (count949 q) 1 2 (meaning938 q) (meaning946 q) (meaning951 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 946 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 946 = false ∨ valuation q 951 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 939 = false ∨ valuationOf q 945 = false ∨ valuationOf q 951 = true := by
  have hs : count949 q = (countLit q [-81, -83, -87]) + (countLit q [-88, -90, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-81, -83, -87]) (l₂ := [-88, -90, -92, -94])
  have hm := merge_two (literal (valuationOf q) (939)) (literal (valuationOf q) (945)) (literal (valuationOf q) (951)) (countLit q [-81, -83, -87]) (countLit q [-88, -90, -92, -94]) (count949 q) 2 1 (meaning939 q) (meaning945 q) (meaning951 q) hs
  change valuationOf q 939 = false ∨ valuationOf q 945 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 939 = false ∨ valuation q 945 = false ∨ valuation q 951 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 956 = true := by
  have hs : count956 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (956)) (countLit q [-95]) (countLit q [-97]) (count956 q) 1 (meaningNeg95 q) (meaning956 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 956 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 958 = true := by
  have hs : count958 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (958)) (countLit q [-100]) (countLit q [-102]) (count958 q) 1 (meaningNeg100 q) (meaning958 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 958 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 960 = true := by
  have hs : count960 q = (countLit q [-95, -97]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-100, -102])
  have hm := merge_right (literal (valuationOf q) (958)) (literal (valuationOf q) (960)) (countLit q [-95, -97]) (countLit q [-100, -102]) (count960 q) 1 (meaning958 q) (meaning960 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 960 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 956 = false ∨ valuationOf q 960 = true := by
  have hs : count960 q = (countLit q [-95, -97]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-100, -102])
  have hm := merge_left (literal (valuationOf q) (956)) (literal (valuationOf q) (960)) (countLit q [-95, -97]) (countLit q [-100, -102]) (count960 q) 1 (meaning956 q) (meaning960 q) hs
  change valuationOf q 956 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 956 = false ∨ valuation q 960 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 964 = true := by
  have hs : count964 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (964)) (countLit q [-103]) (countLit q [-105]) (count964 q) 1 (meaningNeg103 q) (meaning964 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 964 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 966 = true := by
  have hs : count966 q = (countLit q [-108]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-110])
  have hm := merge_right (literal (valuationOf q) (-110)) (literal (valuationOf q) (966)) (countLit q [-108]) (countLit q [-110]) (count966 q) 1 (meaningNeg110 q) (meaning966 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 966 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 966 = true := by
  have hs : count966 q = (countLit q [-108]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-108)) (literal (valuationOf q) (966)) (countLit q [-108]) (countLit q [-110]) (count966 q) 1 (meaningNeg108 q) (meaning966 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 966 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 966 = false ∨ valuationOf q 968 = true := by
  have hs : count968 q = (countLit q [-103, -105]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-108, -110])
  have hm := merge_right (literal (valuationOf q) (966)) (literal (valuationOf q) (968)) (countLit q [-103, -105]) (countLit q [-108, -110]) (count968 q) 1 (meaning966 q) (meaning968 q) hs
  change valuationOf q 966 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 966 = false ∨ valuation q 968 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 964 = false ∨ valuationOf q 968 = true := by
  have hs : count968 q = (countLit q [-103, -105]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-108, -110])
  have hm := merge_left (literal (valuationOf q) (964)) (literal (valuationOf q) (968)) (countLit q [-103, -105]) (countLit q [-108, -110]) (count968 q) 1 (meaning964 q) (meaning968 q) hs
  change valuationOf q 964 = false ∨ valuationOf q 968 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 964 = false ∨ valuation q 968 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 964 = false ∨ valuationOf q 966 = false ∨ valuationOf q 969 = true := by
  have hs : count968 q = (countLit q [-103, -105]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-108, -110])
  have hm := merge_two (literal (valuationOf q) (964)) (literal (valuationOf q) (966)) (literal (valuationOf q) (969)) (countLit q [-103, -105]) (countLit q [-108, -110]) (count968 q) 1 1 (meaning964 q) (meaning966 q) (meaning969 q) hs
  change valuationOf q 964 = false ∨ valuationOf q 966 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 964 = false ∨ valuation q 966 = false ∨ valuation q 969 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 968 = false ∨ valuationOf q 972 = true := by
  have hs : count972 q = (countLit q [-95, -97, -100, -102]) + (countLit q [-103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -100, -102]) (l₂ := [-103, -105, -108, -110])
  have hm := merge_right (literal (valuationOf q) (968)) (literal (valuationOf q) (972)) (countLit q [-95, -97, -100, -102]) (countLit q [-103, -105, -108, -110]) (count972 q) 1 (meaning968 q) (meaning972 q) hs
  change valuationOf q 968 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 968 = false ∨ valuation q 972 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 969 = false ∨ valuationOf q 973 = true := by
  have hs : count972 q = (countLit q [-95, -97, -100, -102]) + (countLit q [-103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -100, -102]) (l₂ := [-103, -105, -108, -110])
  have hm := merge_right (literal (valuationOf q) (969)) (literal (valuationOf q) (973)) (countLit q [-95, -97, -100, -102]) (countLit q [-103, -105, -108, -110]) (count972 q) 2 (meaning969 q) (meaning973 q) hs
  change valuationOf q 969 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 969 = false ∨ valuation q 973 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 972 = true := by
  have hs : count972 q = (countLit q [-95, -97, -100, -102]) + (countLit q [-103, -105, -108, -110]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -100, -102]) (l₂ := [-103, -105, -108, -110])
  have hm := merge_left (literal (valuationOf q) (960)) (literal (valuationOf q) (972)) (countLit q [-95, -97, -100, -102]) (countLit q [-103, -105, -108, -110]) (count972 q) 1 (meaning960 q) (meaning972 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 972 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E123.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112123
