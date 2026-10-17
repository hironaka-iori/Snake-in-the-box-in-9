import LocalWindowBridge
import LocalWindowDirKeys

/-!
# From a snake to the direction-aware window certificates

`LocalWindowBridge` maps a window of a snake onto a canonical window by a cube
automorphism.  This module states the general form needed for the 145 direction
certificates: for any canonical direction list `cs` and any coordinate list `u`
without repetitions that relabels the snake's directions onto `cs`
(`u[cs[j]] = dir p (r + j)`), a certificate `Refuted (winOf cs) (boundsOf syms)` excludes
the lumped counts `syms` on that window (`refuted_dir`).

The relabelling by first occurrence (`WindowAutomaton.canon`) and the lookup in the
exclusion table `forbMask` are handled in `work/spectral/stronger/DirectionWindowBridge.lean`.
-/

namespace Snake9.LocalWindow
open Snake9

set_option maxHeartbeats 1000000

/-! ## The canonical window of a direction list -/

theorem winGo_length : ∀ (v : Nat) (cs : List Nat), (winGo v cs).length = cs.length + 1
  | _, [] => rfl
  | v, _ :: cs => by simp only [winGo, List.length_cons, winGo_length _ cs]

theorem winGo_getD_zero (v : Nat) : ∀ cs : List Nat, (winGo v cs).getD 0 0 = v
  | [] => rfl
  | _ :: _ => rfl

theorem winGo_step : ∀ (cs : List Nat) (v j : Nat), j < cs.length →
    (winGo v cs).getD (j + 1) 0 = (winGo v cs).getD j 0 ^^^ 2 ^ (cs.getD j 0)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | d :: cs, v, 0, _ => by
    simp only [winGo, List.getD_cons_succ, List.getD_cons_zero]
    exact winGo_getD_zero _ cs
  | d :: cs, v, j + 1, h => by
    simp only [winGo, List.getD_cons_succ]
    exact winGo_step cs _ j (by simp only [List.length_cons] at h; omega)

theorem canon_winOf (cs : List Nat) : Canon (winOf cs) cs :=
  ⟨winGo_length 0 cs, winGo_getD_zero 0 cs, fun j hj => winGo_step cs 0 j hj⟩

/-! ## Lumped counts -/

/-- Counts above six are lumped (the same function as `WindowAutomaton.sym`). -/
def symC (a : Nat) : Nat := if a ≤ 6 then a else 6

theorem symC_le_six (a : Nat) : symC a ≤ 6 := by
  unfold symC
  split <;> omega

theorem boundOf_symC {a : Nat} (h : a ≤ 21) :
    (boundOf (symC a)).1 ≤ a ∧ a ≤ (boundOf (symC a)).2 := by
  unfold boundOf symC
  by_cases h6 : a ≤ 6
  · rw [if_pos h6]
    by_cases h5 : a < 6
    · rw [if_pos h5]; exact ⟨Nat.le_refl a, Nat.le_refl a⟩
    · rw [if_neg h5]; exact ⟨by omega, h⟩
  · rw [if_neg h6, if_neg (by omega)]
    exact ⟨by omega, h⟩

theorem freePairs_length : ∀ a, a < 9 → ∀ b, b < 9 → a ≠ b → (freePairs a b).length = 21 := by
  decide

/-- An internal vertex has at most 21 singleton squares. -/
theorem coreAlpha_le_21 {m : Nat} (p : Snake m) {k : Nat} (h0 : 0 < k) (hm : k < m) :
    coreAlpha p k ≤ 21 := by
  rw [← absentCorners_eq_coreAlpha p h0 hm]
  have h1 := dir_lt p (j := k - 1) (by omega)
  have h2 := dir_lt p (j := k) hm
  have hne : dir p (k - 1) ≠ dir p k := by
    have := dir_ne_succ p (j := k - 1) (by omega)
    rwa [show k - 1 + 1 = k by omega] at this
  unfold absentCorners
  rw [← freePairs_length _ h1 _ h2 hne]
  exact List.length_filter_le _ _

theorem getD_boundsOf {syms : List Nat} {i : Nat} (hi : i < syms.length) :
    (boundsOf syms).getD i (0, 21) = boundOf (syms.getD i 0) := by
  simp [boundsOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-! ## The bridge -/

/-- A direction certificate excludes its lumped counts on every snake window whose
directions are relabelled onto `cs` by the duplicate-free coordinate list `u`. -/
theorem refuted_dir {cs syms u : List Nat} (h : Refuted (winOf cs) (boundsOf syms))
    {m : Nat} (p : Snake m) (r : Nat) (hlen : syms.length + 1 = cs.length)
    (hr : r + cs.length ≤ m) (hu : u.Nodup) (hu9 : ∀ d ∈ u, d < 9)
    (hcs : ∀ j, j < cs.length → cs.getD j 0 < u.length ∧ u.getD (cs.getD j 0) 0 = dir p (r + j))
    (hs : ∀ i, i < syms.length → syms.getD i 0 = symC (coreAlpha p (r + i + 1))) : False := by
  have hlen9 : u.length ≤ 9 := by
    have := nodup_length_le_of_subset (l' := List.range 9) hu
      (fun x hx => List.mem_range.2 (hu9 x hx))
    simpa using this
  have hsp := mkPerm_spec hu hu9 hlen9
  refine refuted_bridge p (mkPerm u) r h (canon_winOf cs) (by simp [boundsOf, hlen]) hr ?_ ?_
  · intro j hj
    obtain ⟨h1, h2⟩ := hcs j hj
    rw [← h2]
    exact hsp _ h1
  · intro i hi
    have hi' : i < syms.length := by simpa [boundsOf] using hi
    rw [getD_boundsOf hi', hs i hi']
    exact boundOf_symC (coreAlpha_le_21 p (by omega) (by omega))

#print axioms refuted_dir

end Snake9.LocalWindow
