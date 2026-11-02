import HistoryPrefix
import Mathlib.Data.List.Nodup
namespace Snake9.History75
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
def prefixes : List (List Nat) := [
  [],
  [26],
  [27],
  [29],
  [35],
  [54],
  [66],
  [90],
  [99],
  [139],
  [147],
  [175],
  [177],
  [215],
  [219],
  [235],
  [258],
  [264],
  [281],
  [302],
  [305],
  [350],
  [351],
  [353],
  [354],
  [395],
  [426],
  [440],
  [460],
  [462],
  [479],
  [496],
  [26, 215],
  [27, 219],
  [29, 235],
  [35, 350],
  [35, 351],
  [54, 300],
  [66, 438],
  [66, 439],
  [90, 139],
  [99, 147],
  [139, 350],
  [139, 353],
  [147, 460],
  [175, 50],
  [177, 54],
  [177, 55],
  [215, 79],
  [219, 34],
  [219, 35],
  [235, 79],
  [258, 350],
  [258, 354],
  [264, 395],
  [281, 460],
  [302, 90],
  [305, 99],
  [350, 181],
  [350, 182],
  [351, 171],
  [351, 172],
  [353, 177],
  [354, 181],
  [354, 182],
  [395, 460],
  [426, 281],
  [440, 302],
  [460, 350],
  [460, 352],
  [460, 353],
  [462, 350],
  [462, 353],
  [479, 395],
  [496, 460]
]
def signatures : List (List Nat) := [
  [54, 300, 99],
  [66, 438, 302],
  [66, 439, 299],
  [177, 54, 300],
  [177, 55, 301],
  [258, 350, 180],
  [258, 354, 180],
  [350, 181, 73],
  [139, 353, 177],
  [460, 350, 180],
  [460, 353, 177],
  [26, 215, 79],
  [27, 219, 34],
  [27, 219, 35],
  [29, 235, 79],
  [35, 350, 180],
  [35, 351, 172],
  [90, 139, 350],
  [90, 139, 354],
  [99, 147, 460],
  [99, 147, 461],
  [99, 147, 462],
  [139, 350, 179],
  [147, 460, 350],
  [147, 460, 351],
  [147, 460, 352],
  [147, 460, 354],
  [175, 50, 264],
  [177, 55, 305],
  [215, 79, 462],
  [219, 34, 348],
  [219, 35, 351],
  [235, 79, 462],
  [264, 395, 460],
  [264, 395, 462],
  [281, 460, 354],
  [302, 90, 139],
  [305, 99, 147],
  [350, 182, 78],
  [351, 171, 35],
  [351, 172, 39],
  [353, 177, 55],
  [354, 181, 73],
  [354, 182, 78],
  [395, 460, 354],
  [426, 281, 460],
  [426, 281, 462],
  [440, 302, 90],
  [460, 350, 183],
  [460, 352, 175],
  [462, 350, 180],
  [462, 350, 181],
  [462, 350, 182],
  [462, 350, 183],
  [462, 353, 177],
  [479, 395, 460],
  [479, 395, 462],
  [496, 460, 354]
]

theorem prefixes_empty : ([] : List Nat) ∈ prefixes := by decide
theorem prefixes_length : prefixes.length = 75 := by decide
theorem prefixes_nodup : prefixes.Nodup := by decide
theorem prefixes_closed : PrefixClosed prefixes := by unfold PrefixClosed; decide
theorem prefixes_le_two : ∀ p ∈ prefixes, p.length ≤ 2 := by decide
theorem signatures_valid : ∀ s ∈ signatures, s.length = 3 ∧ s.dropLast ∈ prefixes := by decide

theorem prefix_index_unique (i j : Fin prefixes.length)
    (h : prefixes.get i = prefixes.get j) : i = j :=
  prefixes_nodup.get_inj_iff.mp h

theorem exact_history_invariant (w : List Nat) :
    IsLongest prefixes w (run prefixes w) :=
  run_is_longest prefixes_empty prefixes_closed w

theorem exact_history_update (w : List Nat) (a : Nat) :
    longest prefixes (longest prefixes w ++ [a]) = longest prefixes (w ++ [a]) :=
  longest_update_eq prefixes_empty prefixes_closed w a

theorem exact_signature_sound (w : List Nat) (a : Nat) (sig : List Nat)
    (hsig : sig ∈ signatures) (hemit : sig <:+ run prefixes w ++ [a]) :
    sig = (w ++ [a]).drop ((w ++ [a]).length - 3) :=
  emitted_three_is_last_three prefixes_empty prefixes_closed w a sig
    (signatures_valid sig hsig).1 hemit

theorem exact_no_early_emission (w : List Nat) (a : Nat) (hshort : w.length < 2)
    (sig : List Nat) (hsig : sig ∈ signatures) :
    ¬ sig <:+ run prefixes w ++ [a] :=
  no_emission_first_two prefixes_empty prefixes_closed w a hshort sig
    (signatures_valid sig hsig).1

#print axioms prefixes_empty
#print axioms prefixes_length
#print axioms prefixes_nodup
#print axioms prefixes_closed
#print axioms prefixes_le_two
#print axioms signatures_valid
#print axioms prefix_index_unique
#print axioms exact_history_invariant
#print axioms exact_history_update
#print axioms exact_signature_sound
#print axioms exact_no_early_emission
end Snake9.History75
