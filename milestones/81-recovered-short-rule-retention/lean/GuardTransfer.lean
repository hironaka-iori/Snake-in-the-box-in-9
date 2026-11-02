import PositionTransfer

namespace Snake9.ShortRules81
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.GraphWalk78 Snake9.CountGeometry78 Snake9.GraphInterpretation75
set_option maxHeartbeats 2000000

inductive CountTest where
  | caps : List (Nat × Nat) → CountTest
  | sum : List Nat → Nat → CountTest
  deriving DecidableEq

def CountTest.positions : CountTest → List Nat
  | .caps bounds => bounds.map Prod.fst
  | .sum positions _ => positions

def rawBad (test : CountTest) (count : Nat → Nat) : Prop :=
  match test with
  | .caps bounds => ∀ b ∈ bounds, count b.1 ≤ b.2
  | .sum positions cap => (positions.map count).sum ≤ cap

def encodedBad (test : CountTest) (count : Nat → Nat) : Prop :=
  match test with
  | .caps bounds => ∀ b ∈ bounds, count b.1 ≤ b.2
  | .sum positions cap => (positions.map count).sum ≤ cap ∧ ∀ j ∈ positions, count j < 6

def smallCaps : CountTest → Prop
  | .caps bounds => ∀ b ∈ bounds, b.2 < 6
  | .sum _ _ => True

def internalPositions (test : CountTest) (L : Nat) : Prop :=
  ∀ j ∈ test.positions, 1 ≤ j ∧ j < L

def rawSafe (dirs : List Nat) (test : CountTest) : Prop :=
  ∀ {m : Nat} (p : Snake m) (r : Nat), r+dirs.length ≤ m →
    canon (dsOf p r dirs.length) = dirs → ¬ rawBad test (fun j => coreAlpha p (r+j))

theorem encodedBad_to_raw (test : CountTest) (f g : Nat → Nat)
    (hsmall : smallCaps test)
    (heq : ∀ j ∈ test.positions, f j = min 6 (g j))
    (hbad : encodedBad test f) : rawBad test g := by
  cases test with
  | caps bounds =>
    intro b hb
    have hj : b.1 ∈ CountTest.positions (.caps bounds) :=
      List.mem_map.mpr ⟨b,hb,rfl⟩
    have h := hbad b hb
    rw [heq _ hj] at h
    exact (truncated_guard _ _ (hsmall b hb)).mp h
  | sum positions cap =>
    have he : ∀ j ∈ positions, f j = g j := by
      intro j hj
      have h := hbad.2 j hj
      rw [heq j hj] at h
      exact (heq j hj).trans (unsaturated_exact _ h)
    have hm : positions.map f = positions.map g := by
      apply List.map_congr_left
      exact he
    change (positions.map g).sum ≤ cap
    rw [← hm]
    exact hbad.1

theorem encoded_guard_retention (dirs : List Nat) (test : CountTest)
    (hsafe : rawSafe dirs test) (hsmall : smallCaps test)
    (hint : internalPositions test dirs.length)
    {m : Nat} (p : Snake m) (r offset : Nat) (reverse : Bool)
    (hr : r+9 ≤ m) (ho : offset+dirs.length ≤ 9)
    (hpos : ∀ j ∈ test.positions, 3 ≤ offset+orientedPosition dirs.length reverse j ∧
      offset+orientedPosition dirs.length reverse j ≤ 8)
    (hshape : canon (if reverse then
        (((canon (dsOf p r 9)).drop offset).take dirs.length).reverse
        else ((canon (dsOf p r 9)).drop offset).take dirs.length) = dirs) :
    ¬ encodedBad test (fun j => digit (sixCode p r)
      (offset+orientedPosition dirs.length reverse j-3)) := by
  intro hbad
  apply hsafe (orientedSnake p reverse) (orientedStart m r offset dirs.length reverse)
    (oriented_window_fits p r offset dirs.length reverse hr ho)
    ((oriented_shape p r offset dirs.length reverse hr ho).trans hshape)
  apply encodedBad_to_raw test _ _ hsmall _ hbad
  intro j hj
  exact encoded_oriented_count p r offset dirs.length j reverse hr ho
    (by have h := (hint j hj).2; omega) (hpos j hj)

theorem caps_from_refuted (dirs : List Nat) (caps : List (Nat × Nat))
    (bounds : List (Nat × Nat)) (hlen : bounds.length+1 = dirs.length)
    (href : Refuted (winOf dirs) bounds)
    (hcover : ∀ i, i < bounds.length → (bounds.getD i (0,21)).1 = 0 ∧
      ((bounds.getD i (0,21)).2 = 21 ∨
        ∃ b ∈ caps, b.1 = i+1 ∧ b.2 ≤ (bounds.getD i (0,21)).2)) :
    rawSafe dirs (.caps caps) := by
  intro m p r hr hshape hbad
  apply canonical_interval_exclusion p r dirs.length dirs bounds hr hlen hshape href
  intro i hi
  obtain ⟨hlo,hhi⟩ := hcover i hi
  rw [hlo]
  refine ⟨Nat.zero_le _, ?_⟩
  rcases hhi with hhi | ⟨b,hb,hpos,hcap⟩
  · rw [hhi]
    exact coreAlpha_le_21 p (by omega) (by omega)
  · have h := hbad b hb
    rw [hpos] at h
    dsimp only at h
    have he : r+(i+1) = r+i+1 := by omega
    rw [he] at h
    exact h.trans hcap

theorem digit_one_iff_cap_one (code j : Nat) : digit code j = 1 ↔ digit code j ≤ 1 := by
  unfold digit
  omega

#print axioms encodedBad_to_raw
#print axioms encoded_guard_retention
#print axioms caps_from_refuted
#print axioms digit_one_iff_cap_one
end Snake9.ShortRules81
