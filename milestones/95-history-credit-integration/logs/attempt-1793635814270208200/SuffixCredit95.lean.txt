import CreditTransport95

/-! Generic transfer from the final nine directions of an eleven-word.
Concrete geometry remains a supplied premise. Source awaits compilation. -/

namespace Snake9.CreditTransport95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.HistoryShare94 Snake9.History84

def LocalNineShare (cs : List Nat) (L : Nat) : Prop :=
  ∀ {m : Nat} (p : Snake m) (P : CPerm) (s : Nat), s+9 ≤ m →
    (∀ j, j < cs.length → P.fwd (dir p (s+j)) = cs.getD j 0) →
    L ≤ ((List.range 5).map fun i => coreShare 12 p (s+(i+4))).sum

/-- Shifting the window by two shifts its five centres from offsets 4--8
to offsets 6--10 of the original eleven-word. -/
theorem word_share_of_final_nine (cs ds : List Nat) (L : Nat)
    (hlen : ds.length = 9)
    (hsuffix : canon ((cs.drop 2).take 9) = ds)
    (hlocal : LocalNineShare ds L) : WordShareBound cs L := by
  intro m p s hr hcanon
  have hs : ds = canon (dsOf p (s+2) 9) := by
    have h := canonical_window_slice p s 11 2 9 hr (by decide)
    rw [hcanon, hsuffix] at h
    exact h
  obtain ⟨P,hP⟩ := canonical_permutation p (s+2) 9 (by omega)
  have hmatch : ∀ j, j < ds.length →
      P.fwd (dir p ((s+2)+j)) = ds.getD j 0 := by
    intro j hj
    have hj9 : j < 9 := by simpa only [hlen] using hj
    have h := hP j hj9
    rw [← hs] at h
    exact h
  have hbound := hlocal p P (s+2) (by omega) hmatch
  have hshift : ∀ i : Nat, (s+2)+(i+4) = s+(i+6) := by
    intro i
    omega
  simpa only [hshift] using hbound

#print axioms word_share_of_final_nine

end Snake9.CreditTransport95
