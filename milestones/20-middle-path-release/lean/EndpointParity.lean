import DfsParity
import Mathlib.Tactic

namespace Snake9.PairedSeed
theorem endpoints_41_67_even {m : Nat} (p : Snake m)
    (h0 : p.vertex 0 = 41) (h1 : p.vertex (Fin.last m) = 67) : m % 2 = 0 := by
  have h := endpoint_parity p
  rw [h0,h1] at h
  change bitParity 67 = (bitParity 41 ^^ (m % 2 == 1)) at h
  have h41 : bitParity 41 = true := by decide
  have h67 : bitParity 67 = true := by decide
  rw [h41,h67] at h
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · exact hm
  · simp [hm] at h

theorem fixed_pair_not191 (p : Snake 191)
    (h0 : p.vertex 0 = 41) (h1 : p.vertex (Fin.last 191) = 67) : False := by
  have h := endpoints_41_67_even p h0 h1
  omega

#print axioms endpoints_41_67_even
#print axioms fixed_pair_not191
end Snake9.PairedSeed
