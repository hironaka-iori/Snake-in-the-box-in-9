module

public import LocalWindowDirBridge
public import LocalWindowFamilies

@[expose] public section

/-!
# Interval-key bridge for the K7 cap-7 route to 230 (milestone 37)

Every certificate of the K7 route is a module `LocalWindowCert.V…` whose only public theorem is

    Snake9.LocalWindow.V….refuted : Refuted (winOf cs) [(lo₀, hi₀), …]

(literal canonical directions `cs`, literal count intervals; `lean435/tools/c230.py`). This module is
what the K7 cover lemma consumes. It depends only on the core stack (`LocalWindowBridge`,
`LocalWindowDirBridge`, `LocalWindowFamilies`), never on the K7 automaton chain.

* `refuted_dir_iv`: an interval certificate excludes, on every snake window whose directions are
  relabelled onto `cs` (by a duplicate-free coordinate list `u`), every count vector inside the
  intervals. This is `refuted_dir` with the bounds given explicitly.
* `AllRefutedIV L`: every key of the list `L` is refuted (one conjunct per key, as the 231 glue).
* `refutedIV_of_main`: a main-line certificate `Refuted (winOf cs) (boundsOf syms)` (233/231 keys,
  already Lean-certified) proves every narrower interval key (`refuted_narrow`). Sub-window reuse
  goes through `refuted_sub` / `refuted_key_sub` of `LocalWindowFamilies` in the same way.
-/

namespace Snake9.C230
open Snake9 Snake9.LocalWindow Snake9.LocalWindow.Families

/-- An interval certificate excludes its counts on every snake window relabelled onto `cs`. -/
theorem refuted_dir_iv {cs u : List Nat} {b : List (Nat × Nat)} (h : Refuted (winOf cs) b)
    {m : Nat} (p : Snake m) (r : Nat) (hlen : b.length + 1 = cs.length)
    (hr : r + cs.length ≤ m) (hu : u.Nodup) (hu9 : ∀ d ∈ u, d < 9)
    (hcs : ∀ j, j < cs.length → cs.getD j 0 < u.length ∧ u.getD (cs.getD j 0) 0 = dir p (r + j))
    (hb : ∀ i, i < b.length → (b.getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ (b.getD i (0, 21)).2) : False := by
  have hlen9 : u.length ≤ 9 := by
    have := nodup_length_le_of_subset (l' := List.range 9) hu
      (fun x hx => List.mem_range.2 (hu9 x hx))
    simpa using this
  have hsp := mkPerm_spec hu hu9 hlen9
  refine refuted_bridge p (mkPerm u) r h (canon_winOf cs) hlen hr ?_ hb
  intro j hj
  obtain ⟨h1, h2⟩ := hcs j hj
  rw [← h2]
  exact hsp _ h1

/-- Every key of a list of interval keys is refuted. -/
def AllRefutedIV : List (List Nat × List (Nat × Nat)) → Prop
  | [] => True
  | k :: ks => Refuted (winOf k.1) k.2 ∧ AllRefutedIV ks

theorem AllRefutedIV.get : ∀ {L : List (List Nat × List (Nat × Nat))}, AllRefutedIV L →
    ∀ k ∈ L, Refuted (winOf k.1) k.2
  | [], _, _, hk => absurd hk (List.not_mem_nil)
  | _ :: _, ⟨h, hL⟩, k, hk => by
    rcases List.mem_cons.1 hk with rfl | hk
    · exact h
    · exact AllRefutedIV.get hL k hk

theorem allRefutedIV_append : ∀ {a b : List (List Nat × List (Nat × Nat))},
    AllRefutedIV a → AllRefutedIV b → AllRefutedIV (a ++ b)
  | [], _, _, hb => hb
  | _ :: _, _, ⟨h, ha⟩, hb => ⟨h, allRefutedIV_append ha hb⟩

/-- Reuse of a main-line certificate: a lumped key refutes every narrower interval key. -/
theorem refutedIV_of_main {cs syms : List Nat} {b : List (Nat × Nat)}
    (h : Refuted (winOf cs) (boundsOf syms)) (hw : widerB (boundsOf syms) b = true) :
    Refuted (winOf cs) b :=
  refuted_narrow h hw

/-- The form the chain needs: no snake window of a listed key has its counts in the key's
intervals. -/
theorem no_window_of_list {L : List (List Nat × List (Nat × Nat))} (hL : AllRefutedIV L)
    {cs : List Nat} {b : List (Nat × Nat)} (hk : (cs, b) ∈ L)
    {m : Nat} (p : Snake m) (r : Nat) (hlen : b.length + 1 = cs.length)
    (hr : r + cs.length ≤ m) {u : List Nat} (hu : u.Nodup) (hu9 : ∀ d ∈ u, d < 9)
    (hcs : ∀ j, j < cs.length → cs.getD j 0 < u.length ∧ u.getD (cs.getD j 0) 0 = dir p (r + j))
    (hb : ∀ i, i < b.length → (b.getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ (b.getD i (0, 21)).2) : False :=
  refuted_dir_iv (hL.get _ hk) p r hlen hr hu hu9 hcs hb

end Snake9.C230
