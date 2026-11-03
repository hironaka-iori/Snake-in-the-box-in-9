import ActualCount137
import Mathlib.Tactic

namespace Snake9.Credit139
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow

theorem clipped_pair_sound {a b : Nat}
    (ha : min a 6 < 6) (hb : min b 6 < 6)
    (h : min a 6 + min b 6 ≤ 9) : a + b ≤ 9 := by
  omega

theorem counted_suffixes_le_twenty_four {m : Nat} (p : Snake m) (F : Finset Nat)
    (hfit : ∀ r ∈ F, r+9 ≤ m)
    (hshape : ∀ r ∈ F, canon (dsOf p (r+3) 6) = [0,1,2,0,3,2])
    (ha : ∀ r ∈ F, min (coreAlpha p (r+5)) 6 < 6)
    (hb : ∀ r ∈ F, min (coreAlpha p (r+7)) 6 < 6)
    (hpair : ∀ r ∈ F,
      min (coreAlpha p (r+5)) 6 + min (coreAlpha p (r+7)) 6 ≤ 9) :
    F.card ≤ 24 := by
  classical
  let S := F.image (fun r => r+3)
  have hs : S.card ≤ 24 := ActualCount137.low_pair_count_le_twenty_four p S
    (by
      intro s hs
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hs
      have := hfit r hr
      omega)
    (by
      intro s hs
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hs
      exact hshape r hr)
    (by
      intro s hs
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hs
      have h := clipped_pair_sound (ha r hr) (hb r hr) (hpair r hr)
      simpa only [Nat.add_assoc] using h)
  have hc : S.card = F.card := Finset.card_image_of_injOn (by
    intro r hr s hs heq
    exact Nat.add_right_cancel heq)
  omega

#print axioms clipped_pair_sound
#print axioms counted_suffixes_le_twenty_four
end Snake9.Credit139
