import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-98, -99]) + (countLit q [-104, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-104, -105])
  have hm := merge_right (literal (valuationOf q) (858)) (literal (valuationOf q) (860)) (countLit q [-98, -99]) (countLit q [-104, -105]) (count860 q) 1 (meaning858 q) (meaning860 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 860 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 861 = true := by
  have hs : count860 q = (countLit q [-98, -99]) + (countLit q [-104, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-104, -105])
  have hm := merge_right (literal (valuationOf q) (859)) (literal (valuationOf q) (861)) (countLit q [-98, -99]) (countLit q [-104, -105]) (count860 q) 2 (meaning859 q) (meaning861 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 861 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-98, -99]) + (countLit q [-104, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-104, -105])
  have hm := merge_left (literal (valuationOf q) (856)) (literal (valuationOf q) (860)) (countLit q [-98, -99]) (countLit q [-104, -105]) (count860 q) 1 (meaning856 q) (meaning860 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 860 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 858 = false ∨ valuationOf q 861 = true := by
  have hs : count860 q = (countLit q [-98, -99]) + (countLit q [-104, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-104, -105])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (858)) (literal (valuationOf q) (861)) (countLit q [-98, -99]) (countLit q [-104, -105]) (count860 q) 1 1 (meaning856 q) (meaning858 q) (meaning861 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 858 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 858 = false ∨ valuation q 861 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 864 = true := by
  have hs : count864 q = (countLit q [-92, -95, -97]) + (countLit q [-98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-92, -95, -97]) (l₂ := [-98, -99, -104, -105])
  have hm := merge_right (literal (valuationOf q) (860)) (literal (valuationOf q) (864)) (countLit q [-92, -95, -97]) (countLit q [-98, -99, -104, -105]) (count864 q) 1 (meaning860 q) (meaning864 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 864 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-92, -95, -97]) + (countLit q [-98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-92, -95, -97]) (l₂ := [-98, -99, -104, -105])
  have hm := merge_right (literal (valuationOf q) (861)) (literal (valuationOf q) (865)) (countLit q [-92, -95, -97]) (countLit q [-98, -99, -104, -105]) (count864 q) 2 (meaning861 q) (meaning865 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 865 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 860 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-92, -95, -97]) + (countLit q [-98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-92, -95, -97]) (l₂ := [-98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (860)) (literal (valuationOf q) (865)) (countLit q [-92, -95, -97]) (countLit q [-98, -99, -104, -105]) (count864 q) 1 1 (meaning853 q) (meaning860 q) (meaning865 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 860 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 860 = false ∨ valuation q 865 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 861 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-92, -95, -97]) + (countLit q [-98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-92, -95, -97]) (l₂ := [-98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (861)) (literal (valuationOf q) (866)) (countLit q [-92, -95, -97]) (countLit q [-98, -99, -104, -105]) (count864 q) 1 2 (meaning853 q) (meaning861 q) (meaning866 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 861 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 861 = false ∨ valuation q 866 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 860 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-92, -95, -97]) + (countLit q [-98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-92, -95, -97]) (l₂ := [-98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (860)) (literal (valuationOf q) (866)) (countLit q [-92, -95, -97]) (countLit q [-98, -99, -104, -105]) (count864 q) 2 1 (meaning854 q) (meaning860 q) (meaning866 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 860 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 860 = false ∨ valuation q 866 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-80, -82, -84, -86, -87, -90]) + (countLit q [-92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84, -86, -87, -90]) (l₂ := [-92, -95, -97, -98, -99, -104, -105])
  have hm := merge_right (literal (valuationOf q) (864)) (literal (valuationOf q) (871)) (countLit q [-80, -82, -84, -86, -87, -90]) (countLit q [-92, -95, -97, -98, -99, -104, -105]) (count871 q) 1 (meaning864 q) (meaning871 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 871 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 873 = true := by
  have hs : count871 q = (countLit q [-80, -82, -84, -86, -87, -90]) + (countLit q [-92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84, -86, -87, -90]) (l₂ := [-92, -95, -97, -98, -99, -104, -105])
  have hm := merge_right (literal (valuationOf q) (866)) (literal (valuationOf q) (873)) (countLit q [-80, -82, -84, -86, -87, -90]) (countLit q [-92, -95, -97, -98, -99, -104, -105]) (count871 q) 3 (meaning866 q) (meaning873 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 873 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 864 = false ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-80, -82, -84, -86, -87, -90]) + (countLit q [-92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84, -86, -87, -90]) (l₂ := [-92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (864)) (literal (valuationOf q) (872)) (countLit q [-80, -82, -84, -86, -87, -90]) (countLit q [-92, -95, -97, -98, -99, -104, -105]) (count871 q) 1 1 (meaning845 q) (meaning864 q) (meaning872 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 864 = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 864 = false ∨ valuation q 872 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 865 = false ∨ valuationOf q 873 = true := by
  have hs : count871 q = (countLit q [-80, -82, -84, -86, -87, -90]) + (countLit q [-92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84, -86, -87, -90]) (l₂ := [-92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (865)) (literal (valuationOf q) (873)) (countLit q [-80, -82, -84, -86, -87, -90]) (countLit q [-92, -95, -97, -98, -99, -104, -105]) (count871 q) 1 2 (meaning845 q) (meaning865 q) (meaning873 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 865 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 865 = false ∨ valuation q 873 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 866 = false ∨ valuationOf q 874 = true := by
  have hs : count871 q = (countLit q [-80, -82, -84, -86, -87, -90]) + (countLit q [-92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84, -86, -87, -90]) (l₂ := [-92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (866)) (literal (valuationOf q) (874)) (countLit q [-80, -82, -84, -86, -87, -90]) (countLit q [-92, -95, -97, -98, -99, -104, -105]) (count871 q) 1 3 (meaning845 q) (meaning866 q) (meaning874 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 866 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 866 = false ∨ valuation q 874 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 864 = false ∨ valuationOf q 873 = true := by
  have hs : count871 q = (countLit q [-80, -82, -84, -86, -87, -90]) + (countLit q [-92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84, -86, -87, -90]) (l₂ := [-92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (864)) (literal (valuationOf q) (873)) (countLit q [-80, -82, -84, -86, -87, -90]) (countLit q [-92, -95, -97, -98, -99, -104, -105]) (count871 q) 2 1 (meaning846 q) (meaning864 q) (meaning873 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 864 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 864 = false ∨ valuation q 873 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 865 = false ∨ valuationOf q 874 = true := by
  have hs : count871 q = (countLit q [-80, -82, -84, -86, -87, -90]) + (countLit q [-92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84, -86, -87, -90]) (l₂ := [-92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (865)) (literal (valuationOf q) (874)) (countLit q [-80, -82, -84, -86, -87, -90]) (countLit q [-92, -95, -97, -98, -99, -104, -105]) (count871 q) 2 2 (meaning846 q) (meaning865 q) (meaning874 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 865 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 865 = false ∨ valuation q 874 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 864 = false ∨ valuationOf q 874 = true := by
  have hs : count871 q = (countLit q [-80, -82, -84, -86, -87, -90]) + (countLit q [-92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -84, -86, -87, -90]) (l₂ := [-92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (864)) (literal (valuationOf q) (874)) (countLit q [-80, -82, -84, -86, -87, -90]) (countLit q [-92, -95, -97, -98, -99, -104, -105]) (count871 q) 3 1 (meaning847 q) (meaning864 q) (meaning874 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 864 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 864 = false ∨ valuation q 874 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 826 = false ∨ valuationOf q 871 = false ∨ valuationOf q 883 = true := by
  have hs : count881 q = (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) + (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (l₂ := [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (826)) (literal (valuationOf q) (871)) (literal (valuationOf q) (883)) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count881 q) 2 1 (meaning826 q) (meaning871 q) (meaning883 q) hs
  change valuationOf q 826 = false ∨ valuationOf q 871 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 826 = false ∨ valuation q 871 = false ∨ valuation q 883 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 826 = false ∨ valuationOf q 873 = false ∨ valuationOf q 885 = true := by
  have hs : count881 q = (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) + (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (l₂ := [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (826)) (literal (valuationOf q) (873)) (literal (valuationOf q) (885)) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count881 q) 2 3 (meaning826 q) (meaning873 q) (meaning885 q) hs
  change valuationOf q 826 = false ∨ valuationOf q 873 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 826 = false ∨ valuation q 873 = false ∨ valuation q 885 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 826 = false ∨ valuationOf q 874 = false ∨ valuationOf q 886 = true := by
  have hs : count881 q = (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) + (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (l₂ := [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (826)) (literal (valuationOf q) (874)) (literal (valuationOf q) (886)) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count881 q) 2 4 (meaning826 q) (meaning874 q) (meaning886 q) hs
  change valuationOf q 826 = false ∨ valuationOf q 874 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 826 = false ∨ valuation q 874 = false ∨ valuation q 886 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 872 = false ∨ valuationOf q 885 = true := by
  have hs : count881 q = (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) + (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (l₂ := [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (872)) (literal (valuationOf q) (885)) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count881 q) 3 2 (meaning827 q) (meaning872 q) (meaning885 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 872 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 872 = false ∨ valuation q 885 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 873 = false ∨ valuationOf q 886 = true := by
  have hs : count881 q = (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) + (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (l₂ := [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (873)) (literal (valuationOf q) (886)) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count881 q) 3 3 (meaning827 q) (meaning873 q) (meaning886 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 873 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 873 = false ∨ valuation q 886 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 874 = false ∨ valuationOf q 887 = true := by
  have hs : count881 q = (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) + (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (l₂ := [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (874)) (literal (valuationOf q) (887)) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count881 q) 3 4 (meaning827 q) (meaning874 q) (meaning887 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 874 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 874 = false ∨ valuation q 887 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 872 = false ∨ valuationOf q 886 = true := by
  have hs : count881 q = (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) + (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (l₂ := [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (828)) (literal (valuationOf q) (872)) (literal (valuationOf q) (886)) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count881 q) 4 2 (meaning828 q) (meaning872 q) (meaning886 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 872 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 872 = false ∨ valuation q 886 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 873 = false ∨ valuationOf q 887 = true := by
  have hs : count881 q = (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) + (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (l₂ := [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (828)) (literal (valuationOf q) (873)) (literal (valuationOf q) (887)) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count881 q) 4 3 (meaning828 q) (meaning873 q) (meaning887 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 873 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 873 = false ∨ valuation q 887 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 874 = false ∨ valuationOf q 888 = true := by
  have hs : count881 q = (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) + (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (l₂ := [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (828)) (literal (valuationOf q) (874)) (literal (valuationOf q) (888)) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count881 q) 4 4 (meaning828 q) (meaning874 q) (meaning888 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 874 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 874 = false ∨ valuation q 888 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 829 = false ∨ valuationOf q 872 = false ∨ valuationOf q 887 = true := by
  have hs : count881 q = (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) + (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (l₂ := [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (829)) (literal (valuationOf q) (872)) (literal (valuationOf q) (887)) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count881 q) 5 2 (meaning829 q) (meaning872 q) (meaning887 q) hs
  change valuationOf q 829 = false ∨ valuationOf q 872 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 829 = false ∨ valuation q 872 = false ∨ valuation q 887 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 829 = false ∨ valuationOf q 873 = false ∨ valuationOf q 888 = true := by
  have hs : count881 q = (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) + (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (l₂ := [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (829)) (literal (valuationOf q) (873)) (literal (valuationOf q) (888)) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count881 q) 5 3 (meaning829 q) (meaning873 q) (meaning888 q) hs
  change valuationOf q 829 = false ∨ valuationOf q 873 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 829 = false ∨ valuation q 873 = false ∨ valuation q 888 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 829 = false ∨ valuationOf q 874 = false ∨ valuationOf q 889 = true := by
  have hs : count881 q = (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) + (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (l₂ := [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (829)) (literal (valuationOf q) (874)) (literal (valuationOf q) (889)) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]) (countLit q [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count881 q) 5 4 (meaning829 q) (meaning874 q) (meaning889 q) hs
  change valuationOf q 829 = false ∨ valuationOf q 874 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 829 = false ∨ valuation q 874 = false ∨ valuation q 889 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 783 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true := by
  have hs : count891 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) + (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (l₂ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (783)) (literal (valuationOf q) (889)) (literal (valuationOf q) (900)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count891 q) 1 9 (meaning783 q) (meaning889 q) (meaning900 q) hs
  change valuationOf q 783 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 783 = false ∨ valuation q 889 = false ∨ valuation q 900 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 784 = false ∨ valuationOf q 888 = false ∨ valuationOf q 900 = true := by
  have hs : count891 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) + (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (l₂ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (784)) (literal (valuationOf q) (888)) (literal (valuationOf q) (900)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count891 q) 2 8 (meaning784 q) (meaning888 q) (meaning900 q) hs
  change valuationOf q 784 = false ∨ valuationOf q 888 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 784 = false ∨ valuation q 888 = false ∨ valuation q 900 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 785 = false ∨ valuationOf q 887 = false ∨ valuationOf q 900 = true := by
  have hs : count891 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) + (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (l₂ := [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105])
  have hm := merge_two (literal (valuationOf q) (785)) (literal (valuationOf q) (887)) (literal (valuationOf q) (900)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (countLit q [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]) (count891 q) 3 7 (meaning785 q) (meaning887 q) (meaning900 q) hs
  change valuationOf q 785 = false ∨ valuationOf q 887 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 785 = false ∨ valuation q 887 = false ∨ valuation q 900 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E075.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112075
