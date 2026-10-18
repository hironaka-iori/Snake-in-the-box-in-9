/-
The direction-aware window premises of the conditional bound 238 from the 325
five-centre window certificates.

Core Lean only (imports the standard-library core modules `LocalWindowDirBridge`,
`LocalWindowDirKeys5` and `PathStructure`).  Same construction as
`DirectionWindowBridge` for the 145 certificates of the bound 239:

* `cover_table5` (kernel evaluation, one theorem per window length): every bit of the
  exclusion table `forbMask5` that is looked up for a canonical shape of two to five
  centres belongs to one of the 325 certificate keys `dirKeys5` (`LocalWindowDirKeys5.lean`).
  Shapes outside the 9 listed ones use the empty slot 9 of the table
  (`unlisted_zero`), so only listed shapes are enumerated: this keeps the kernel's term cache
  small (a lookup shifts the whole table).
* `window_refute5`: a window of a snake whose canonical shape and lumped counts hit a
  set bit contradicts the corresponding certificate (`refuted_dir` realises the
  first-occurrence relabelling `canon` by a coordinate permutation).
* `no_forb_window5`: the reversed lookup in `wforb5` is the same statement for the
  reversed snake.
* `direction_windows_core5`: the four premises of `upper_238_of_direction_windows5`,
  with the singleton count `coreAlpha` in place of `countSeq`.
-/
import WindowAutomaton5Data
import WindowAutomatonLemmas
import WindowAutomatonBridge
import DirectionWindowBridge
import LocalWindowDirKeys5

namespace Snake9.DirectionWindow5
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow

set_option maxHeartbeats 1000000

/-! ## The 325 keys cover the exclusion table -/

/-- The bit of `forbMask5` looked up by `wforb5a` for the canonical shape `c`. -/
def forbBit5 (c syms : List Nat) : Bool :=
  (forbMask5 >>> (wshapeIdx5 (shapeCode c) * 16807 + symIdx syms 0)) &&& 1 == 1

theorem wforb5a_eq (ds syms : List Nat) : wforb5a ds syms = forbBit5 (canon ds) syms := rfl

/-- Slot 9 of the table (unlisted shapes) is empty. -/
theorem unlisted_zero : forbMask5 >>> (9 * 16807) = 0 := by decide +kernel

theorem forbBit5_unlisted (c syms : List Nat) (h : wshapeIdx5 (shapeCode c) = 9) :
    forbBit5 c syms = false := by
  unfold forbBit5
  rw [h, Nat.shiftRight_add, unlisted_zero, Nat.zero_shiftRight]
  rfl

def coverOK5 (c : List Nat) : Bool :=
  wshapeIdx5 (shapeCode c) == 9 ||
  allSyms0 (c.length - 1) (fun syms => !forbBit5 c syms || decide ((c, syms) ∈ dirKeys5))

set_option maxRecDepth 100000 in
theorem cover_table5_3 : allRGS 3 0 coverOK5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cover_table5_4 : allRGS 4 0 coverOK5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cover_table5_5 : allRGS 5 0 coverOK5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cover_table5_6 : allRGS 6 0 coverOK5 = true := by decide +kernel

/-- Conversely every one of the 325 keys is a set bit (not needed for the bound; it
confirms that the key list and the table agree exactly). -/
theorem keys_in_table5 :
    (dirKeys5.length == 325 && dirKeys5.all (fun k => forbBit5 k.1 k.2)) = true := by
  decide +kernel

theorem cover5 {c syms : List Nat} (hc : isRGS c 0 = true)
    (hn : c.length = 3 ∨ c.length = 4 ∨ c.length = 5 ∨ c.length = 6)
    (hl : syms.length = c.length - 1)
    (hs : ∀ s ∈ syms, s ≤ 6) (hb : forbBit5 c syms = true) : (c, syms) ∈ dirKeys5 := by
  have hok : coverOK5 c = true := by
    rcases hn with hn | hn | hn | hn
    · exact allRGS_spec 3 0 _ cover_table5_3 c hn hc
    · exact allRGS_spec 4 0 _ cover_table5_4 c hn hc
    · exact allRGS_spec 5 0 _ cover_table5_5 c hn hc
    · exact allRGS_spec 6 0 _ cover_table5_6 c hn hc
  unfold coverOK5 at hok
  rcases Bool.or_eq_true_iff.1 hok with hu | hok
  · have hu' : wshapeIdx5 (shapeCode c) = 9 := by simpa using hu
    rw [forbBit5_unlisted c syms hu'] at hb
    exact absurd hb (by decide)
  · have := allSyms0_spec _ _ hok syms hl hs
    simpa [hb] using this

/-! ## Windows of a snake -/

section Window
variable {m : Nat} (p : Snake m)

/-- A window whose canonical shape and lumped counts hit a set bit of `forbMask5`
contradicts the certificate of that key. -/
theorem window_refute5 (h : AllRefuted238) (r n : Nat) (hn : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6)
    (hr : r + n ≤ m) (hb : wforb5a (dsOf p r n) (symsOf p r n) = true) : False := by
  have hlen := length_dsOf p r n
  have hslen := length_symsOf p r n
  have hkey : (canon (dsOf p r n), symsOf p r n) ∈ dirKeys5 := by
    refine cover5 (canon_isRGS _) (by rw [length_canon]; omega) (by rw [length_canon]; omega)
      ?_ (by rw [← wforb5a_eq]; exact hb)
    intro s hs
    simp only [symsOf, List.mem_map] at hs
    obtain ⟨i, _, rfl⟩ := hs
    exact symC_le_six _
  have href : Refuted (winOf (canon (dsOf p r n))) (boundsOf (symsOf p r n)) :=
    AllRefutedList.mem h _ hkey
  have hmem : ∀ j, j < n → (dsOf p r n).getD j 0 ∈ seenAfter [] (dsOf p r n) := by
    intro j hj
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  refine refuted_dir href p r (u := seenAfter [] (dsOf p r n)) (by rw [length_canon]; omega)
    (by rw [length_canon]; omega) (seenAfter_nodup [] _ List.nodup_nil) ?_ ?_ ?_
  · intro d hd
    rcases mem_seenAfter_cases [] _ d hd with h | h
    · simp at h
    · simp only [dsOf, List.mem_map, List.mem_range] at h
      obtain ⟨j, hj, rfl⟩ := h
      exact dir_lt p (by omega)
  · intro j hj
    rw [length_canon] at hj
    have e : (canon (dsOf p r n)).getD j 0 = idx (seenAfter [] (dsOf p r n)) ((dsOf p r n).getD j 0) := by
      rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    rw [e]
    refine ⟨idx_lt_of_mem _ _ (hmem j (by omega)), ?_⟩
    rw [getD_idx _ _ (hmem j (by omega)), getD_dsOf p (by omega)]
  · intro i hi
    exact getD_symsOf p (by omega)

/-- No window of two to five centres is excluded by `wforb5`, in either orientation. -/
theorem no_forb_window5 (h : AllRefuted238) (r n : Nat) (hn : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6)
    (hr : r + n ≤ m) : wforb5 (dsOf p r n) (symsOf p r n) = false := by
  cases hw : wforb5 (dsOf p r n) (symsOf p r n)
  · rfl
  · exfalso
    unfold wforb5 at hw
    rcases Bool.or_eq_true_iff.1 hw with h1 | h1
    · exact window_refute5 p h r n hn hr h1
    · rw [← dsOf_rev p r n hr, ← symsOf_rev p r n hr] at h1
      exact window_refute5 (revSnake p) h (m - r - n) n hn (by omega) h1

end Window

/-- The premises of `upper_238_of_direction_windows5`, with `coreAlpha` for the
singleton count, from the 325 certificate statements. -/
theorem direction_windows_core5 (h : AllRefuted238) {m : Nat} (p : Snake m) :
    (∀ j, j + 3 ≤ m → wforb5 [pathDir p j, pathDir p (j+1), pathDir p (j+2)]
      [symC (coreAlpha p (j+1)), symC (coreAlpha p (j+2))] = false) ∧
    (∀ j, j + 4 ≤ m → wforb5 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3)]
      [symC (coreAlpha p (j+1)), symC (coreAlpha p (j+2)), symC (coreAlpha p (j+3))] = false) ∧
    (∀ j, j + 5 ≤ m →
      wforb5 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4)]
      [symC (coreAlpha p (j+1)), symC (coreAlpha p (j+2)), symC (coreAlpha p (j+3)),
        symC (coreAlpha p (j+4))] = false) ∧
    (∀ j, j + 6 ≤ m →
      wforb5 [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4),
        pathDir p (j+5)]
      [symC (coreAlpha p (j+1)), symC (coreAlpha p (j+2)), symC (coreAlpha p (j+3)),
        symC (coreAlpha p (j+4)), symC (coreAlpha p (j+5))] = false) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have := no_forb_window5 p h j 3 (by omega) hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
    exact this
  · have := no_forb_window5 p h j 4 (by omega) hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega)]
    exact this
  · have := no_forb_window5 p h j 5 (by omega) hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
    exact this
  · have := no_forb_window5 p h j 6 (by omega) hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
    exact this

#print axioms cover_table5_6
#print axioms direction_windows_core5

end Snake9.DirectionWindow5
