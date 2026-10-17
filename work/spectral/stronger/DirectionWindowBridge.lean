/-
The direction-aware window premises of the conditional bound 239 from the 145
local window certificates.

Core Lean only (imports the standard-library core modules `LocalWindowDirBridge`
and `PathStructure`).

* `cover_table` (kernel evaluation): every bit of the exclusion table `forbMask`
  that is looked up for a canonical shape of two, three or four centres belongs to
  one of the 145 certificate keys `dirKeys` (`LocalWindowDirKeys.lean`).
* `window_refute`: a window of a snake whose canonical shape and lumped counts hit a
  set bit contradicts the corresponding certificate.  The relabelling by first
  occurrence `canon` is realised by a coordinate permutation (`refuted_dir`).
* `no_forb_window`: the reversed lookup in `wforb` is the same statement for the
  reversed snake.
* `direction_windows_core`: the three premises of `upper_239_of_direction_windows`,
  with the singleton count `coreAlpha` in place of `countSeq`.
-/
import WindowAutomatonLemmas
import WindowAutomatonBridge
import LocalWindowDirBridge

namespace Snake9.DirectionWindow
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton

set_option maxHeartbeats 1000000

/-! ## The 145 keys cover the exclusion table -/

/-- All lists of length `n` with entries at most six. -/
def allSyms0 : Nat → (List Nat → Bool) → Bool
  | 0, f => f []
  | n + 1, f => allBelow 7 (fun s => allSyms0 n (fun l => f (s :: l)))

theorem allSyms0_spec : ∀ n (f : List Nat → Bool), allSyms0 n f = true →
    ∀ l : List Nat, l.length = n → (∀ s ∈ l, s ≤ 6) → f l = true
  | 0, _, h, [], _, _ => h
  | 0, _, _, _ :: _, hl, _ => by simp at hl
  | _ + 1, _, _, [], hl, _ => by simp at hl
  | n + 1, f, h, s :: l, hl, hs => by
    have h1 := allBelow_spec 7 _ h s (by have := hs s List.mem_cons_self; omega)
    exact allSyms0_spec n _ h1 l (by simpa using hl) (fun x hx => hs x (List.mem_cons_of_mem _ hx))

/-- The bit of `forbMask` looked up by `wforb1` for the canonical shape `c`. -/
def forbBit (c syms : List Nat) : Bool :=
  (forbMask >>> (wshapeIdx (shapeCode c) * 2401 + symIdx syms 0)) &&& 1 == 1

theorem wforb1_eq (ds syms : List Nat) : wforb1 ds syms = forbBit (canon ds) syms := rfl

def coverOK (c : List Nat) : Bool :=
  allSyms0 (c.length - 1) (fun syms => !forbBit c syms || decide ((c, syms) ∈ dirKeys))

set_option maxRecDepth 100000 in
/-- Every set bit for a restricted growth string of length 3, 4 or 5 and symbols at
most six is a certificate key. -/
theorem cover_table :
    (allRGS 3 0 coverOK && allRGS 4 0 coverOK && allRGS 5 0 coverOK) = true := by
  decide +kernel

/-- Conversely every one of the 145 keys is a set bit (not needed for the bound; it
confirms that the key list and the table agree exactly). -/
theorem keys_in_table : (dirKeys.length == 145 && dirKeys.all (fun k => forbBit k.1 k.2)) = true := by
  decide +kernel

theorem cover {c syms : List Nat} (hc : isRGS c 0 = true)
    (hn : c.length = 3 ∨ c.length = 4 ∨ c.length = 5) (hl : syms.length = c.length - 1)
    (hs : ∀ s ∈ syms, s ≤ 6) (hb : forbBit c syms = true) : (c, syms) ∈ dirKeys := by
  have ht := cover_table
  simp only [Bool.and_eq_true] at ht
  obtain ⟨⟨h3, h4⟩, h5⟩ := ht
  have hok : coverOK c = true := by
    rcases hn with hn | hn | hn
    · exact allRGS_spec 3 0 _ h3 c hn hc
    · exact allRGS_spec 4 0 _ h4 c hn hc
    · exact allRGS_spec 5 0 _ h5 c hn hc
  have := allSyms0_spec _ _ hok syms hl hs
  simpa [hb] using this

/-! ## First-occurrence labels -/

theorem getD_idx : ∀ (u : List Nat) (d : Nat), d ∈ u → u.getD (idx u d) 0 = d
  | [], _, h => absurd h List.not_mem_nil
  | a :: u, d, h => by
    unfold idx
    by_cases had : a = d
    · rw [if_pos had]; simp [had]
    · rw [if_neg had]
      have hd : d ∈ u := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm had
        · exact h
      simp only [List.getD_cons_succ]
      exact getD_idx u d hd

theorem seenAfter_nodup : ∀ (seen ds : List Nat), seen.Nodup → (seenAfter seen ds).Nodup
  | _, [], h => h
  | seen, d :: ds, h => by
    unfold seenAfter
    apply seenAfter_nodup
    split
    · exact h
    · rename_i hd
      show List.Pairwise (· ≠ ·) (seen ++ [d])
      rw [List.pairwise_append]
      refine ⟨h, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro e
      subst e
      exact hd ha

theorem mem_seenAfter_cases : ∀ (seen ds : List Nat) (d : Nat),
    d ∈ seenAfter seen ds → d ∈ seen ∨ d ∈ ds
  | _, [], _, h => Or.inl h
  | seen, a :: ds, d, h => by
    unfold seenAfter at h
    rcases mem_seenAfter_cases _ ds d h with h | h
    · split at h
      · exact Or.inl h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · rw [List.mem_singleton] at h
          subst h
          exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-! ## Windows of a snake -/

section Window
variable {m : Nat} (p : Snake m)

/-- Directions of the `n` path steps starting at index `r`. -/
def dsOf (r n : Nat) : List Nat := (List.range n).map (fun j => dir p (r + j))

/-- Lumped singleton counts of the `n - 1` centres of that window. -/
def symsOf (r n : Nat) : List Nat :=
  (List.range (n - 1)).map (fun i => symC (coreAlpha p (r + i + 1)))

theorem length_dsOf (r n : Nat) : (dsOf p r n).length = n := by simp [dsOf]

theorem length_symsOf (r n : Nat) : (symsOf p r n).length = n - 1 := by simp [symsOf]

theorem getD_dsOf {r n j : Nat} (hj : j < n) : (dsOf p r n).getD j 0 = dir p (r + j) := by
  simp [dsOf, List.getD_eq_getElem?_getD, hj]

theorem getD_symsOf {r n i : Nat} (hi : i < n - 1) :
    (symsOf p r n).getD i 0 = symC (coreAlpha p (r + i + 1)) := by
  simp [symsOf, List.getD_eq_getElem?_getD, hi]

/-- A window whose canonical shape and lumped counts hit a set bit of `forbMask`
contradicts the certificate of that key. -/
theorem window_refute (h : AllRefuted239) (r n : Nat) (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (hr : r + n ≤ m) (hb : wforb1 (dsOf p r n) (symsOf p r n) = true) : False := by
  have hlen := length_dsOf p r n
  have hslen := length_symsOf p r n
  have hkey : (canon (dsOf p r n), symsOf p r n) ∈ dirKeys := by
    refine cover (canon_isRGS _) (by rw [length_canon]; omega) (by rw [length_canon]; omega)
      ?_ (by rw [← wforb1_eq]; exact hb)
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

theorem dsOf_rev (r n : Nat) (hr : r + n ≤ m) :
    dsOf (revSnake p) (m - r - n) n = (dsOf p r n).reverse := by
  apply List.ext_getElem
  · simp [dsOf]
  · intro j h1 h2
    simp only [dsOf, List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_map,
      List.length_range]
    simp only [dsOf, List.length_map, List.length_range] at h1
    rw [dir_rev p (by omega)]
    congr 1
    omega

theorem symsOf_rev (r n : Nat) (hr : r + n ≤ m) :
    symsOf (revSnake p) (m - r - n) n = (symsOf p r n).reverse := by
  apply List.ext_getElem
  · simp [symsOf]
  · intro i h1 h2
    simp only [symsOf, List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_map,
      List.length_range]
    simp only [symsOf, List.length_map, List.length_range] at h1
    rw [coreAlpha_rev p (by omega)]
    congr 2
    omega

/-- No window of two, three or four centres is excluded by `wforb`, in either
orientation. -/
theorem no_forb_window (h : AllRefuted239) (r n : Nat) (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (hr : r + n ≤ m) : wforb (dsOf p r n) (symsOf p r n) = false := by
  cases hw : wforb (dsOf p r n) (symsOf p r n)
  · rfl
  · exfalso
    unfold wforb at hw
    rcases Bool.or_eq_true_iff.1 hw with h1 | h1
    · exact window_refute p h r n hn hr h1
    · rw [← dsOf_rev p r n hr, ← symsOf_rev p r n hr] at h1
      exact window_refute (revSnake p) h (m - r - n) n hn (by omega) h1

end Window

/-! ## Path directions -/

theorem pathDir_eq_dir {m : Nat} (p : Snake m) {j : Nat} (hj : j < m) : pathDir p j = dir p j := by
  have h1 : j + 1 < m + 1 := by omega
  have hadj : Adj (p.vertex ⟨j, by omega⟩) (p.vertex ⟨j + 1, h1⟩) :=
    (path_adj_iff p _ _).mpr (Or.inl rfl)
  have he := WindowAutomaton.adj_dirOf _ _ hadj
  unfold dir vx
  rw [dif_pos (by omega), dif_pos h1, he, dirOfStep_xor]
  unfold pathDir
  rw [dif_pos h1]

/-- The premises of `upper_239_of_direction_windows`, with `coreAlpha` for the
singleton count, from the 145 certificate statements. -/
theorem direction_windows_core (h : AllRefuted239) {m : Nat} (p : Snake m) :
    (∀ j, j + 3 ≤ m → wforb [pathDir p j, pathDir p (j+1), pathDir p (j+2)]
      [symC (coreAlpha p (j+1)), symC (coreAlpha p (j+2))] = false) ∧
    (∀ j, j + 4 ≤ m → wforb [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3)]
      [symC (coreAlpha p (j+1)), symC (coreAlpha p (j+2)), symC (coreAlpha p (j+3))] = false) ∧
    (∀ j, j + 5 ≤ m →
      wforb [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4)]
      [symC (coreAlpha p (j+1)), symC (coreAlpha p (j+2)), symC (coreAlpha p (j+3)),
        symC (coreAlpha p (j+4))] = false) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have := no_forb_window p h j 3 (by omega) hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
    exact this
  · have := no_forb_window p h j 4 (by omega) hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega)]
    exact this
  · have := no_forb_window p h j 5 (by omega) hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
    exact this

#print axioms cover_table
#print axioms direction_windows_core

end Snake9.DirectionWindow
