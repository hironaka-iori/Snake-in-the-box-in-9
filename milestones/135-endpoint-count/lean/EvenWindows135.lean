import DfsParity
import LocalWindowBridge

namespace Snake9.EvenWindows135
open Snake9.LocalWindow

set_option maxHeartbeats 2000000

theorem common_neighbor_even_index {m : Nat} (p : Snake m) (r z : Nat)
    (hr : r ≤ m) (hz : z < 512)
    (hzero : vx p 0 ∈ nbrs z) (hvertex : vx p r ∈ nbrs z) :
    r % 2 = 0 := by
  have hpar : ∀ w ∈ nbrs z, bitParity w = !bitParity z := by
    intro w hw
    obtain ⟨k,hk,he⟩ := (mem_nbrs z w).mp hw
    rw [he]
    exact bitParity_flip ⟨z,hz⟩ ⟨k,hk⟩
  have hequal : bitParity (vx p r) = bitParity (vx p 0) :=
    (hpar _ hvertex).trans (hpar _ hzero).symm
  have hrpos : r < m+1 := by omega
  have h0pos : 0 < m+1 := by omega
  have hp : bitParity (vx p r) =
      (bitParity (vx p 0) ^^ (r % 2 == 1)) := by
    simpa only [vx,dif_pos hrpos,dif_pos h0pos] using parity_along p r hr
  rw [hequal] at hp
  rcases Nat.mod_two_eq_zero_or_one r with h | h
  · exact h
  · cases hb : bitParity (vx p 0) <;> simp [h,hb] at hp

theorem unit_neighbor_even_start {m : Nat} (p : Snake m) (r a : Nat)
    (hr : r ≤ m) (ha : a < 9) (hzero : vx p 0 = 0)
    (hvertex : vx p r ∈ nbrs (2^a)) : r % 2 = 0 := by
  have hz : 2^a < 512 := by
    simpa only [Nat.zero_xor] using xor_pow_lt (v := 0) (by decide) ha
  have h0 : vx p 0 ∈ nbrs (2^a) := by
    apply (mem_nbrs _ _).mpr
    exact ⟨a,ha,by rw [hzero,Nat.xor_self]⟩
  exact common_neighbor_even_index p r (2^a) hr hz h0 hvertex

theorem unit_neighbor_even_index {m : Nat} (p : Snake m) (r a : Nat)
    (hr : r ≤ m) (ha : a < 9) (hzero : vx p 0 = 0)
    (hvertex : vx p r ∈ nbrs (2^a)) : ∃ t, r=2*t := by
  have h := unit_neighbor_even_start p r a hr ha hzero hvertex
  exact ⟨r/2,by omega⟩

#print axioms common_neighbor_even_index
#print axioms unit_neighbor_even_start
#print axioms unit_neighbor_even_index
end Snake9.EvenWindows135
