import EndpointGeometry122
import ReferenceInterface

namespace Snake9.EndpointFrequency122
open Snake9.LocalWindow Snake9.EndpointGeometry122
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem hamming_comm (u v : Nat) : hamming u v = hamming v u := by
  unfold hamming
  rw [Nat.xor_comm]

theorem hamming_xor (t u v : Nat) :
    hamming (t ^^^ u) (t ^^^ v) = hamming u v := by
  have he : (t ^^^ u) ^^^ (t ^^^ v) = (t ^^^ t) ^^^ (u ^^^ v) := by
    ac_rfl
  simp only [hamming, he, Nat.xor_self, Nat.zero_xor]

-- The distance-two sphere of zero is represented by its 36 coordinate pairs.
theorem zero_sphere_mem : ∀ v : Fin 512, hamming 0 v.val = 2 →
    v.val ∈ ((freePairs 9 9).map (fun ab => 2^ab.1 ^^^ 2^ab.2)).toFinset := by
  decide +kernel

-- Only 511 nonzero endpoint differences and 36 possible centre vertices occur.
theorem intersection_card_le : ∀ d : Fin 512, d.val ≠ 0 →
    ((((freePairs 9 9).map (fun ab => 2^ab.1 ^^^ 2^ab.2)).toFinset).filter
      (fun v => hamming d.val v = 2)).card ≤ 14 := by
  decide +kernel

theorem window_count_le_fourteen {m : Nat} (p : Snake m) (I : Finset Nat)
    (hfit : ∀ r ∈ I, r+6 ≤ m)
    (hend : ∀ r ∈ I,
      hamming (vx p (r+2)) (vx p 0) = 2 ∧
      hamming (vx p (r+2)) (vx p m) = 2) :
    I.card ≤ 14 := by
  by_cases hI : I = ∅
  · simp [hI]
  obtain ⟨r₀,hr₀⟩ := Finset.nonempty_iff_ne_empty.mpr hI
  have hm : 0 < m := by have h := hfit r₀ hr₀; omega
  let t := vx p 0
  let d := t ^^^ vx p m
  let f : Nat → Nat := fun r => t ^^^ vx p (r+2)
  let T := ((freePairs 9 9).map (fun ab => 2^ab.1 ^^^ 2^ab.2)).toFinset
  have hdlt : d < 512 :=
    Nat.xor_lt_two_pow (n := 9) (vx_lt p 0) (vx_lt p m)
  have hne : vx p 0 ≠ vx p m := by
    intro he
    have hi := vx_inj p (i := 0) (j := m) (by omega) (by omega) he
    omega
  have hdne : d ≠ 0 := by
    intro he
    have hx := congrArg (fun z => t ^^^ z) he
    change t ^^^ (t ^^^ vx p m) = t ^^^ 0 at hx
    have hz : vx p m = t := by
      simpa only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero] using hx
    exact hne hz.symm
  have hcard : (T.filter (fun v => hamming d v = 2)).card ≤ 14 :=
    intersection_card_le ⟨d,hdlt⟩ hdne
  have hbound : I.card ≤ (T.filter (fun v => hamming d v = 2)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro r hr
      have hfr : f r < 512 :=
        Nat.xor_lt_two_pow (n := 9) (vx_lt p 0) (vx_lt p (r+2))
      have hrends := hend r hr
      have hzero : hamming 0 (f r) = 2 := by
        have hx := hamming_xor t t (vx p (r+2))
        rw [Nat.xor_self] at hx
        exact hx.trans ((hamming_comm t (vx p (r+2))).trans hrends.1)
      have hdist : hamming d (f r) = 2 :=
        (hamming_xor t (vx p m) (vx p (r+2))).trans
          ((hamming_comm (vx p m) (vx p (r+2))).trans hrends.2)
      exact Finset.mem_filter.mpr ⟨zero_sphere_mem ⟨f r,hfr⟩ hzero,hdist⟩
    · intro r hr s hs he
      have hv : vx p (r+2) = vx p (s+2) := xor_left_inj t he
      have hi := vx_inj p (i := r+2) (j := s+2)
        (by have h := hfit r hr; omega) (by have h := hfit s hs; omega) hv
      omega
  exact hbound.trans hcard

#print axioms hamming_comm
#print axioms hamming_xor
#print axioms zero_sphere_mem
#print axioms intersection_card_le
#print axioms window_count_le_fourteen
end Snake9.EndpointFrequency122
