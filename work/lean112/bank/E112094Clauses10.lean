import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 744 = false ∨ valuationOf q 747 = false ∨ valuationOf q 753 = true := by
  have hs : count750 q = (countLit q [-26, -27, -30]) + (countLit q [-32, -34, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -30]) (l₂ := [-32, -34, -35])
  have hm := merge_two (literal (valuationOf q) (744)) (literal (valuationOf q) (747)) (literal (valuationOf q) (753)) (countLit q [-26, -27, -30]) (countLit q [-32, -34, -35]) (count750 q) 3 1 (meaning744 q) (meaning747 q) (meaning753 q) hs
  change valuationOf q 744 = false ∨ valuationOf q 747 = false ∨ valuationOf q 753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 744 = false ∨ valuation q 747 = false ∨ valuation q 753 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 758 = true := by
  have hs : count758 q = (countLit q [-37]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39, -42])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (758)) (countLit q [-37]) (countLit q [-39, -42]) (count758 q) 1 (meaningNeg37 q) (meaning758 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 758 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 763 = true := by
  have hs : count763 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (763)) (countLit q [-48]) (countLit q [-50]) (count763 q) 1 (meaningNeg48 q) (meaning763 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 763 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 763 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 763 = false ∨ valuationOf q 765 = true := by
  have hs : count765 q = (countLit q [-43, -46]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-48, -50])
  have hm := merge_right (literal (valuationOf q) (763)) (literal (valuationOf q) (765)) (countLit q [-43, -46]) (countLit q [-48, -50]) (count765 q) 1 (meaning763 q) (meaning765 q) hs
  change valuationOf q 763 = false ∨ valuationOf q 765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 763 = false ∨ valuation q 765 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 769 = true := by
  have hs : count769 q = (countLit q [-37, -39, -42]) + (countLit q [-43, -46, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -42]) (l₂ := [-43, -46, -48, -50])
  have hm := merge_left (literal (valuationOf q) (758)) (literal (valuationOf q) (769)) (countLit q [-37, -39, -42]) (countLit q [-43, -46, -48, -50]) (count769 q) 1 (meaning758 q) (meaning769 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 769 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 765 = false ∨ valuationOf q 770 = true := by
  have hs : count769 q = (countLit q [-37, -39, -42]) + (countLit q [-43, -46, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -42]) (l₂ := [-43, -46, -48, -50])
  have hm := merge_two (literal (valuationOf q) (758)) (literal (valuationOf q) (765)) (literal (valuationOf q) (770)) (countLit q [-37, -39, -42]) (countLit q [-43, -46, -48, -50]) (count769 q) 1 1 (meaning758 q) (meaning765 q) (meaning770 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 765 = false ∨ valuationOf q 770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 765 = false ∨ valuation q 770 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 750 = false ∨ valuationOf q 769 = false ∨ valuationOf q 777 = true := by
  have hs : count776 q = (countLit q [-26, -27, -30, -32, -34, -35]) + (countLit q [-37, -39, -42, -43, -46, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -30, -32, -34, -35]) (l₂ := [-37, -39, -42, -43, -46, -48, -50])
  have hm := merge_two (literal (valuationOf q) (750)) (literal (valuationOf q) (769)) (literal (valuationOf q) (777)) (countLit q [-26, -27, -30, -32, -34, -35]) (countLit q [-37, -39, -42, -43, -46, -48, -50]) (count776 q) 1 1 (meaning750 q) (meaning769 q) (meaning777 q) hs
  change valuationOf q 750 = false ∨ valuationOf q 769 = false ∨ valuationOf q 777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 750 = false ∨ valuation q 769 = false ∨ valuation q 777 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 750 = false ∨ valuationOf q 770 = false ∨ valuationOf q 778 = true := by
  have hs : count776 q = (countLit q [-26, -27, -30, -32, -34, -35]) + (countLit q [-37, -39, -42, -43, -46, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -30, -32, -34, -35]) (l₂ := [-37, -39, -42, -43, -46, -48, -50])
  have hm := merge_two (literal (valuationOf q) (750)) (literal (valuationOf q) (770)) (literal (valuationOf q) (778)) (countLit q [-26, -27, -30, -32, -34, -35]) (countLit q [-37, -39, -42, -43, -46, -48, -50]) (count776 q) 1 2 (meaning750 q) (meaning770 q) (meaning778 q) hs
  change valuationOf q 750 = false ∨ valuationOf q 770 = false ∨ valuationOf q 778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 750 = false ∨ valuation q 770 = false ∨ valuation q 778 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 753 = false ∨ valuationOf q 769 = false ∨ valuationOf q 780 = true := by
  have hs : count776 q = (countLit q [-26, -27, -30, -32, -34, -35]) + (countLit q [-37, -39, -42, -43, -46, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -30, -32, -34, -35]) (l₂ := [-37, -39, -42, -43, -46, -48, -50])
  have hm := merge_two (literal (valuationOf q) (753)) (literal (valuationOf q) (769)) (literal (valuationOf q) (780)) (countLit q [-26, -27, -30, -32, -34, -35]) (countLit q [-37, -39, -42, -43, -46, -48, -50]) (count776 q) 4 1 (meaning753 q) (meaning769 q) (meaning780 q) hs
  change valuationOf q 753 = false ∨ valuationOf q 769 = false ∨ valuationOf q 780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 753 = false ∨ valuation q 769 = false ∨ valuation q 780 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 729 = false ∨ valuationOf q 780 = false ∨ valuationOf q 792 = true := by
  have hs : count787 q = (countLit q [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23]) + (countLit q [-26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23]) (l₂ := [-26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50])
  have hm := merge_two (literal (valuationOf q) (729)) (literal (valuationOf q) (780)) (literal (valuationOf q) (792)) (countLit q [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23]) (countLit q [-26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) (count787 q) 1 5 (meaning729 q) (meaning780 q) (meaning792 q) hs
  change valuationOf q 729 = false ∨ valuationOf q 780 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 729 = false ∨ valuation q 780 = false ∨ valuation q 792 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 730 = false ∨ valuationOf q 777 = false ∨ valuationOf q 790 = true := by
  have hs : count787 q = (countLit q [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23]) + (countLit q [-26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23]) (l₂ := [-26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50])
  have hm := merge_two (literal (valuationOf q) (730)) (literal (valuationOf q) (777)) (literal (valuationOf q) (790)) (countLit q [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23]) (countLit q [-26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) (count787 q) 2 2 (meaning730 q) (meaning777 q) (meaning790 q) hs
  change valuationOf q 730 = false ∨ valuationOf q 777 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 730 = false ∨ valuation q 777 = false ∨ valuation q 790 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 730 = false ∨ valuationOf q 778 = false ∨ valuationOf q 791 = true := by
  have hs : count787 q = (countLit q [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23]) + (countLit q [-26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23]) (l₂ := [-26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50])
  have hm := merge_two (literal (valuationOf q) (730)) (literal (valuationOf q) (778)) (literal (valuationOf q) (791)) (countLit q [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23]) (countLit q [-26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]) (count787 q) 2 3 (meaning730 q) (meaning778 q) (meaning791 q) hs
  change valuationOf q 730 = false ∨ valuationOf q 778 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 730 = false ∨ valuation q 778 = false ∨ valuation q 791 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 845 = true := by
  have hs : count845 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (845)) (countLit q [-81]) (countLit q [-83]) (count845 q) 1 (meaningNeg81 q) (meaning845 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 845 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 845 = false ∨ valuationOf q 848 = true := by
  have hs : count847 q = (countLit q [-79]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81, -83])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (845)) (literal (valuationOf q) (848)) (countLit q [-79]) (countLit q [-81, -83]) (count847 q) 1 1 (meaningNeg79 q) (meaning845 q) (meaning848 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 845 = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 845 = false ∨ valuation q 848 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 850 = true := by
  have hs : count850 q = (countLit q [-88]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (850)) (countLit q [-88]) (countLit q [-89]) (count850 q) 1 (meaningNeg88 q) (meaning850 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 850 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 850 = false ∨ valuationOf q 852 = true := by
  have hs : count852 q = (countLit q [-85]) + (countLit q [-88, -89]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-88, -89])
  have hm := merge_right (literal (valuationOf q) (850)) (literal (valuationOf q) (852)) (countLit q [-85]) (countLit q [-88, -89]) (count852 q) 1 (meaning850 q) (meaning852 q) hs
  change valuationOf q 850 = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 850 = false ∨ valuation q 852 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 852 = false ∨ valuationOf q 857 = true := by
  have hs : count855 q = (countLit q [-79, -81, -83]) + (countLit q [-85, -88, -89]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -83]) (l₂ := [-85, -88, -89])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (852)) (literal (valuationOf q) (857)) (countLit q [-79, -81, -83]) (countLit q [-85, -88, -89]) (count855 q) 2 1 (meaning848 q) (meaning852 q) (meaning857 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 852 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 852 = false ∨ valuation q 857 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 94 = true ∨ valuationOf q 862 = true := by
  have hs : count861 q = (countLit q [-91]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (862)) (countLit q [-91]) (countLit q [-94]) (count861 q) 1 1 (meaningNeg91 q) (meaningNeg94 q) (meaning862 q) hs
  change (! (valuationOf q 91)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 94 = true ∨ valuation q 862 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 862 = false ∨ valuationOf q 865 = true := by
  have hs : count863 q = (countLit q [-90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91, -94])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (862)) (literal (valuationOf q) (865)) (countLit q [-90]) (countLit q [-91, -94]) (count863 q) 1 2 (meaningNeg90 q) (meaning862 q) (meaning865 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 862 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 862 = false ∨ valuation q 865 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 866 = true := by
  have hs : count866 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (866)) (countLit q [-96]) (countLit q [-98]) (count866 q) 1 (meaningNeg98 q) (meaning866 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 866 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 98 = true ∨ valuationOf q 867 = true := by
  have hs : count866 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (867)) (countLit q [-96]) (countLit q [-98]) (count866 q) 1 1 (meaningNeg96 q) (meaningNeg98 q) (meaning867 q) hs
  change (! (valuationOf q 96)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 98 = true ∨ valuation q 867 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 868 = true := by
  have hs : count868 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (868)) (countLit q [-100]) (countLit q [-102]) (count868 q) 1 (meaningNeg102 q) (meaning868 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 868 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 868 = true := by
  have hs : count868 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (868)) (countLit q [-100]) (countLit q [-102]) (count868 q) 1 (meaningNeg100 q) (meaning868 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 868 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 870 = true := by
  have hs : count870 q = (countLit q [-96, -98]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -102])
  have hm := merge_right (literal (valuationOf q) (868)) (literal (valuationOf q) (870)) (countLit q [-96, -98]) (countLit q [-100, -102]) (count870 q) 1 (meaning868 q) (meaning870 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 870 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 870 = true := by
  have hs : count870 q = (countLit q [-96, -98]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -102])
  have hm := merge_left (literal (valuationOf q) (866)) (literal (valuationOf q) (870)) (countLit q [-96, -98]) (countLit q [-100, -102]) (count870 q) 1 (meaning866 q) (meaning870 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 870 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 871 = true := by
  have hs : count870 q = (countLit q [-96, -98]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -102])
  have hm := merge_left (literal (valuationOf q) (867)) (literal (valuationOf q) (871)) (countLit q [-96, -98]) (countLit q [-100, -102]) (count870 q) 2 (meaning867 q) (meaning871 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 871 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 876 = true := by
  have hs : count874 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -98, -100, -102])
  have hm := merge_left (literal (valuationOf q) (865)) (literal (valuationOf q) (876)) (countLit q [-90, -91, -94]) (countLit q [-96, -98, -100, -102]) (count874 q) 3 (meaning865 q) (meaning876 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 876 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 870 = false ∨ valuationOf q 877 = true := by
  have hs : count874 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (870)) (literal (valuationOf q) (877)) (countLit q [-90, -91, -94]) (countLit q [-96, -98, -100, -102]) (count874 q) 3 1 (meaning865 q) (meaning870 q) (meaning877 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 870 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 870 = false ∨ valuation q 877 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 871 = false ∨ valuationOf q 878 = true := by
  have hs : count874 q = (countLit q [-90, -91, -94]) + (countLit q [-96, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94]) (l₂ := [-96, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (871)) (literal (valuationOf q) (878)) (countLit q [-90, -91, -94]) (countLit q [-96, -98, -100, -102]) (count874 q) 3 2 (meaning865 q) (meaning871 q) (meaning878 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 871 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 871 = false ∨ valuation q 878 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 885 = true := by
  have hs : count881 q = (countLit q [-79, -81, -83, -85, -88, -89]) + (countLit q [-90, -91, -94, -96, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -83, -85, -88, -89]) (l₂ := [-90, -91, -94, -96, -98, -100, -102])
  have hm := merge_right (literal (valuationOf q) (878)) (literal (valuationOf q) (885)) (countLit q [-79, -81, -83, -85, -88, -89]) (countLit q [-90, -91, -94, -96, -98, -100, -102]) (count881 q) 5 (meaning878 q) (meaning885 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 885 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 876 = false ∨ valuationOf q 886 = true := by
  have hs : count881 q = (countLit q [-79, -81, -83, -85, -88, -89]) + (countLit q [-90, -91, -94, -96, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -83, -85, -88, -89]) (l₂ := [-90, -91, -94, -96, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (876)) (literal (valuationOf q) (886)) (countLit q [-79, -81, -83, -85, -88, -89]) (countLit q [-90, -91, -94, -96, -98, -100, -102]) (count881 q) 3 3 (meaning857 q) (meaning876 q) (meaning886 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 876 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 876 = false ∨ valuation q 886 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 877 = false ∨ valuationOf q 887 = true := by
  have hs : count881 q = (countLit q [-79, -81, -83, -85, -88, -89]) + (countLit q [-90, -91, -94, -96, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -83, -85, -88, -89]) (l₂ := [-90, -91, -94, -96, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (877)) (literal (valuationOf q) (887)) (countLit q [-79, -81, -83, -85, -88, -89]) (countLit q [-90, -91, -94, -96, -98, -100, -102]) (count881 q) 3 4 (meaning857 q) (meaning877 q) (meaning887 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 877 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 877 = false ∨ valuation q 887 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E094.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112094
