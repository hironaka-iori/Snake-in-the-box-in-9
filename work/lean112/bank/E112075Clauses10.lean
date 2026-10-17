import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 704 = false ∨ valuationOf q 707 = true := by
  have hs : count705 q = (countLit q [-1, -3, -6]) + (countLit q [-7, -8, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-7, -8, -13])
  have hm := merge_right (literal (valuationOf q) (704)) (literal (valuationOf q) (707)) (countLit q [-1, -3, -6]) (countLit q [-7, -8, -13]) (count705 q) 3 (meaning704 q) (meaning707 q) hs
  change valuationOf q 704 = false ∨ valuationOf q 707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 704 = false ∨ valuation q 707 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 697 = false ∨ valuationOf q 705 = true := by
  have hs : count705 q = (countLit q [-1, -3, -6]) + (countLit q [-7, -8, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-7, -8, -13])
  have hm := merge_left (literal (valuationOf q) (697)) (literal (valuationOf q) (705)) (countLit q [-1, -3, -6]) (countLit q [-7, -8, -13]) (count705 q) 1 (meaning697 q) (meaning705 q) hs
  change valuationOf q 697 = false ∨ valuationOf q 705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 697 = false ∨ valuation q 705 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 697 = false ∨ valuationOf q 702 = false ∨ valuationOf q 706 = true := by
  have hs : count705 q = (countLit q [-1, -3, -6]) + (countLit q [-7, -8, -13]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-7, -8, -13])
  have hm := merge_two (literal (valuationOf q) (697)) (literal (valuationOf q) (702)) (literal (valuationOf q) (706)) (countLit q [-1, -3, -6]) (countLit q [-7, -8, -13]) (count705 q) 1 1 (meaning697 q) (meaning702 q) (meaning706 q) hs
  change valuationOf q 697 = false ∨ valuationOf q 702 = false ∨ valuationOf q 706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 697 = false ∨ valuation q 702 = false ∨ valuation q 706 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 711 = true := by
  have hs : count711 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (711)) (countLit q [-15]) (countLit q [-17]) (count711 q) 1 (meaningNeg17 q) (meaning711 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 711 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 711 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 711 = true := by
  have hs : count711 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (711)) (countLit q [-15]) (countLit q [-17]) (count711 q) 1 (meaningNeg15 q) (meaning711 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 711 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 711 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 17 = true ∨ valuationOf q 712 = true := by
  have hs : count711 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (712)) (countLit q [-15]) (countLit q [-17]) (count711 q) 1 1 (meaningNeg15 q) (meaningNeg17 q) (meaning712 q) hs
  change (! (valuationOf q 15)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 712 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 712 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 711 = false ∨ valuationOf q 713 = true := by
  have hs : count713 q = (countLit q [-14]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -17])
  have hm := merge_right (literal (valuationOf q) (711)) (literal (valuationOf q) (713)) (countLit q [-14]) (countLit q [-15, -17]) (count713 q) 1 (meaning711 q) (meaning713 q) hs
  change valuationOf q 711 = false ∨ valuationOf q 713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 711 = false ∨ valuation q 713 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 712 = false ∨ valuationOf q 714 = true := by
  have hs : count713 q = (countLit q [-14]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -17])
  have hm := merge_right (literal (valuationOf q) (712)) (literal (valuationOf q) (714)) (countLit q [-14]) (countLit q [-15, -17]) (count713 q) 2 (meaning712 q) (meaning714 q) hs
  change valuationOf q 712 = false ∨ valuationOf q 714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 712 = false ∨ valuation q 714 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 713 = true := by
  have hs : count713 q = (countLit q [-14]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -17])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (713)) (countLit q [-14]) (countLit q [-15, -17]) (count713 q) 1 (meaningNeg14 q) (meaning713 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 713 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 713 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 716 = true := by
  have hs : count716 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (716)) (countLit q [-22]) (countLit q [-23]) (count716 q) 1 (meaningNeg22 q) (meaning716 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 716 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 716 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 716 = false ∨ valuationOf q 718 = true := by
  have hs : count718 q = (countLit q [-20]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22, -23])
  have hm := merge_right (literal (valuationOf q) (716)) (literal (valuationOf q) (718)) (countLit q [-20]) (countLit q [-22, -23]) (count718 q) 1 (meaning716 q) (meaning718 q) hs
  change valuationOf q 716 = false ∨ valuationOf q 718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 716 = false ∨ valuation q 718 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 718 = true := by
  have hs : count718 q = (countLit q [-20]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22, -23])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (718)) (countLit q [-20]) (countLit q [-22, -23]) (count718 q) 1 (meaningNeg20 q) (meaning718 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 718 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 718 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 718 = false ∨ valuationOf q 721 = true := by
  have hs : count721 q = (countLit q [-14, -15, -17]) + (countLit q [-20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -17]) (l₂ := [-20, -22, -23])
  have hm := merge_right (literal (valuationOf q) (718)) (literal (valuationOf q) (721)) (countLit q [-14, -15, -17]) (countLit q [-20, -22, -23]) (count721 q) 1 (meaning718 q) (meaning721 q) hs
  change valuationOf q 718 = false ∨ valuationOf q 721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 718 = false ∨ valuation q 721 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 713 = false ∨ valuationOf q 721 = true := by
  have hs : count721 q = (countLit q [-14, -15, -17]) + (countLit q [-20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -17]) (l₂ := [-20, -22, -23])
  have hm := merge_left (literal (valuationOf q) (713)) (literal (valuationOf q) (721)) (countLit q [-14, -15, -17]) (countLit q [-20, -22, -23]) (count721 q) 1 (meaning713 q) (meaning721 q) hs
  change valuationOf q 713 = false ∨ valuationOf q 721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 713 = false ∨ valuation q 721 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 713 = false ∨ valuationOf q 718 = false ∨ valuationOf q 722 = true := by
  have hs : count721 q = (countLit q [-14, -15, -17]) + (countLit q [-20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -17]) (l₂ := [-20, -22, -23])
  have hm := merge_two (literal (valuationOf q) (713)) (literal (valuationOf q) (718)) (literal (valuationOf q) (722)) (countLit q [-14, -15, -17]) (countLit q [-20, -22, -23]) (count721 q) 1 1 (meaning713 q) (meaning718 q) (meaning722 q) hs
  change valuationOf q 713 = false ∨ valuationOf q 718 = false ∨ valuationOf q 722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 713 = false ∨ valuation q 718 = false ∨ valuation q 722 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 714 = false ∨ valuationOf q 722 = true := by
  have hs : count721 q = (countLit q [-14, -15, -17]) + (countLit q [-20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -17]) (l₂ := [-20, -22, -23])
  have hm := merge_left (literal (valuationOf q) (714)) (literal (valuationOf q) (722)) (countLit q [-14, -15, -17]) (countLit q [-20, -22, -23]) (count721 q) 2 (meaning714 q) (meaning722 q) hs
  change valuationOf q 714 = false ∨ valuationOf q 722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 714 = false ∨ valuation q 722 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 721 = false ∨ valuationOf q 727 = true := by
  have hs : count727 q = (countLit q [-1, -3, -6, -7, -8, -13]) + (countLit q [-14, -15, -17, -20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13]) (l₂ := [-14, -15, -17, -20, -22, -23])
  have hm := merge_right (literal (valuationOf q) (721)) (literal (valuationOf q) (727)) (countLit q [-1, -3, -6, -7, -8, -13]) (countLit q [-14, -15, -17, -20, -22, -23]) (count727 q) 1 (meaning721 q) (meaning727 q) hs
  change valuationOf q 721 = false ∨ valuationOf q 727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 721 = false ∨ valuation q 727 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 722 = false ∨ valuationOf q 728 = true := by
  have hs : count727 q = (countLit q [-1, -3, -6, -7, -8, -13]) + (countLit q [-14, -15, -17, -20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13]) (l₂ := [-14, -15, -17, -20, -22, -23])
  have hm := merge_right (literal (valuationOf q) (722)) (literal (valuationOf q) (728)) (countLit q [-1, -3, -6, -7, -8, -13]) (countLit q [-14, -15, -17, -20, -22, -23]) (count727 q) 2 (meaning722 q) (meaning728 q) hs
  change valuationOf q 722 = false ∨ valuationOf q 728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 722 = false ∨ valuation q 728 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 705 = false ∨ valuationOf q 727 = true := by
  have hs : count727 q = (countLit q [-1, -3, -6, -7, -8, -13]) + (countLit q [-14, -15, -17, -20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13]) (l₂ := [-14, -15, -17, -20, -22, -23])
  have hm := merge_left (literal (valuationOf q) (705)) (literal (valuationOf q) (727)) (countLit q [-1, -3, -6, -7, -8, -13]) (countLit q [-14, -15, -17, -20, -22, -23]) (count727 q) 1 (meaning705 q) (meaning727 q) hs
  change valuationOf q 705 = false ∨ valuationOf q 727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 705 = false ∨ valuation q 727 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 705 = false ∨ valuationOf q 721 = false ∨ valuationOf q 728 = true := by
  have hs : count727 q = (countLit q [-1, -3, -6, -7, -8, -13]) + (countLit q [-14, -15, -17, -20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13]) (l₂ := [-14, -15, -17, -20, -22, -23])
  have hm := merge_two (literal (valuationOf q) (705)) (literal (valuationOf q) (721)) (literal (valuationOf q) (728)) (countLit q [-1, -3, -6, -7, -8, -13]) (countLit q [-14, -15, -17, -20, -22, -23]) (count727 q) 1 1 (meaning705 q) (meaning721 q) (meaning728 q) hs
  change valuationOf q 705 = false ∨ valuationOf q 721 = false ∨ valuationOf q 728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 705 = false ∨ valuation q 721 = false ∨ valuation q 728 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 706 = false ∨ valuationOf q 728 = true := by
  have hs : count727 q = (countLit q [-1, -3, -6, -7, -8, -13]) + (countLit q [-14, -15, -17, -20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13]) (l₂ := [-14, -15, -17, -20, -22, -23])
  have hm := merge_left (literal (valuationOf q) (706)) (literal (valuationOf q) (728)) (countLit q [-1, -3, -6, -7, -8, -13]) (countLit q [-14, -15, -17, -20, -22, -23]) (count727 q) 2 (meaning706 q) (meaning728 q) hs
  change valuationOf q 706 = false ∨ valuationOf q 728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 706 = false ∨ valuation q 728 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 706 = false ∨ valuationOf q 721 = false ∨ valuationOf q 729 = true := by
  have hs : count727 q = (countLit q [-1, -3, -6, -7, -8, -13]) + (countLit q [-14, -15, -17, -20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13]) (l₂ := [-14, -15, -17, -20, -22, -23])
  have hm := merge_two (literal (valuationOf q) (706)) (literal (valuationOf q) (721)) (literal (valuationOf q) (729)) (countLit q [-1, -3, -6, -7, -8, -13]) (countLit q [-14, -15, -17, -20, -22, -23]) (count727 q) 2 1 (meaning706 q) (meaning721 q) (meaning729 q) hs
  change valuationOf q 706 = false ∨ valuationOf q 721 = false ∨ valuationOf q 729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 706 = false ∨ valuation q 721 = false ∨ valuation q 729 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 707 = false ∨ valuationOf q 721 = false ∨ valuationOf q 730 = true := by
  have hs : count727 q = (countLit q [-1, -3, -6, -7, -8, -13]) + (countLit q [-14, -15, -17, -20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13]) (l₂ := [-14, -15, -17, -20, -22, -23])
  have hm := merge_two (literal (valuationOf q) (707)) (literal (valuationOf q) (721)) (literal (valuationOf q) (730)) (countLit q [-1, -3, -6, -7, -8, -13]) (countLit q [-14, -15, -17, -20, -22, -23]) (count727 q) 3 1 (meaning707 q) (meaning721 q) (meaning730 q) hs
  change valuationOf q 707 = false ∨ valuationOf q 721 = false ∨ valuationOf q 730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 707 = false ∨ valuation q 721 = false ∨ valuation q 730 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 737 = true := by
  have hs : count737 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (737)) (countLit q [-29]) (countLit q [-30]) (count737 q) 1 (meaningNeg30 q) (meaning737 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 737 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 737 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 737 = false ∨ valuationOf q 739 = true := by
  have hs : count739 q = (countLit q [-28]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (737)) (literal (valuationOf q) (739)) (countLit q [-28]) (countLit q [-29, -30]) (count739 q) 1 (meaning737 q) (meaning739 q) hs
  change valuationOf q 737 = false ∨ valuationOf q 739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 737 = false ∨ valuation q 739 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 742 = true := by
  have hs : count742 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (742)) (countLit q [-37]) (countLit q [-39]) (count742 q) 1 (meaningNeg39 q) (meaning742 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 742 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 742 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 742 = true := by
  have hs : count742 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (742)) (countLit q [-37]) (countLit q [-39]) (count742 q) 1 (meaningNeg37 q) (meaning742 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 742 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 742 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 39 = true ∨ valuationOf q 743 = true := by
  have hs : count742 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-39)) (literal (valuationOf q) (743)) (countLit q [-37]) (countLit q [-39]) (count742 q) 1 1 (meaningNeg37 q) (meaningNeg39 q) (meaning743 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 39)) = false ∨ valuationOf q 743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 743 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 742 = false ∨ valuationOf q 744 = true := by
  have hs : count744 q = (countLit q [-33]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-37, -39])
  have hm := merge_right (literal (valuationOf q) (742)) (literal (valuationOf q) (744)) (countLit q [-33]) (countLit q [-37, -39]) (count744 q) 1 (meaning742 q) (meaning744 q) hs
  change valuationOf q 742 = false ∨ valuationOf q 744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 742 = false ∨ valuation q 744 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 743 = false ∨ valuationOf q 745 = true := by
  have hs : count744 q = (countLit q [-33]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-37, -39])
  have hm := merge_right (literal (valuationOf q) (743)) (literal (valuationOf q) (745)) (countLit q [-33]) (countLit q [-37, -39]) (count744 q) 2 (meaning743 q) (meaning745 q) hs
  change valuationOf q 743 = false ∨ valuationOf q 745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 743 = false ∨ valuation q 745 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 744 = true := by
  have hs : count744 q = (countLit q [-33]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-37, -39])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (744)) (countLit q [-33]) (countLit q [-37, -39]) (count744 q) 1 (meaningNeg33 q) (meaning744 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 744 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 744 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 742 = false ∨ valuationOf q 745 = true := by
  have hs : count744 q = (countLit q [-33]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-37, -39])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (742)) (literal (valuationOf q) (745)) (countLit q [-33]) (countLit q [-37, -39]) (count744 q) 1 1 (meaningNeg33 q) (meaning742 q) (meaning745 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 742 = false ∨ valuationOf q 745 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 742 = false ∨ valuation q 745 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E075.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112075
