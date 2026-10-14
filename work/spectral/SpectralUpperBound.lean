import Archive.Sensitivity
import Snake9
import Mathlib.Tactic

namespace Snake9
open Sensitivity
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def encode (v : Vertex) : Q 9 := fun k => v.val.testBit k.val

theorem high_bit_false (v : Vertex) (k : Nat) (hk : 9 ≤ k) :
    v.val.testBit k = false := by
  apply Nat.testBit_lt_two_pow
  have hpow : 2^9 ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
  have hv := v.isLt
  norm_num at hpow
  omega

theorem encode_injective : Function.Injective encode := by
  intro u v he
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 9
  · exact congrFun he ⟨k,hk⟩
  · rw [high_bit_false u k (by omega), high_bit_false v k (by omega)]

theorem adjacent_decode (u v : Vertex) (h : encode v ∈ (encode u).adjacent) :
    Adj u v := by
  rcases h with ⟨k,hk,unique⟩
  apply (adj_iff_coordinate_flip u v).mpr
  refine ⟨k.val,k.isLt,?_⟩
  apply Nat.eq_of_testBit_eq
  intro i
  change v.val.testBit i = (u.val ^^^ 2^k.val).testBit i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hi : i = k.val
  · subst i
    change u.val.testBit k.val ≠ v.val.testBit k.val at hk
    cases hu : u.val.testBit k.val <;> cases hv : v.val.testBit k.val <;> simp_all
  · have he : u.val.testBit i = v.val.testBit i := by
      by_cases hil : i < 9
      · by_contra hne
        have heq := unique ⟨i,hil⟩ hne
        have := congrArg Fin.val heq
        exact hi this
      · rw [high_bit_false u i (by omega), high_bit_false v i (by omega)]
    simp [Ne.symm hi, he]

theorem cube_adjacent_symm {u v : Q 9} (h : v ∈ u.adjacent) : u ∈ v.adjacent := by
  rcases h with ⟨k,hk,unique⟩
  exact ⟨k,Ne.symm hk,fun i hi => unique i (Ne.symm hi)⟩

theorem snake_degree_le_two {m : Nat} (p : Snake m) (i : Fin (m+1)) :
    ((Set.range (fun j => encode (p.vertex j))) ∩ (encode (p.vertex i)).adjacent).toFinset.card ≤ 2 := by
  classical
  let f := fun j => encode (p.vertex j)
  let left : Fin (m+1) := ⟨i.val-1,by omega⟩
  let right : Fin (m+1) := ⟨min (i.val+1) m,by omega⟩
  have subset : ((Set.range f) ∩ (f i).adjacent).toFinset ⊆ {f left,f right} := by
    intro v hv
    have hv' : v ∈ Set.range f ∩ (f i).adjacent := Set.mem_toFinset.mp hv
    rcases hv' with ⟨⟨j,rfl⟩,hij⟩
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · have hstep := (p.induced i j hlt).mp (adjacent_decode _ _ hij)
      have hj : j = right := by
        apply Fin.ext
        dsimp [right]
        have hjbound := j.isLt
        omega
      simp [hj]
    · have hji : i = j := Fin.ext heq
      subst j
      rcases hij with ⟨k,hk,_⟩
      exact (hk rfl).elim
    · have hstep := (p.induced j i hgt).mp (adjacent_decode _ _ (cube_adjacent_symm hij))
      have hj : j = left := by apply Fin.ext; dsimp [left]; omega
      simp [hj]
  have hp : ({f left,f right} : Finset (Q 9)).card ≤ 2 := by
    simpa using Finset.card_insert_le (f left) ({f right} : Finset (Q 9))
  exact le_trans (Finset.card_le_card subset) hp

theorem universal_upper_bound_255 {m : Nat} (p : Snake m) : m ≤ 255 := by
  classical
  let f := fun j => encode (p.vertex j)
  let H : Set (Q 9) := Set.range f
  have hf : Function.Injective f := encode_injective.comp p.distinct
  have hcard : H.ncard = m+1 := by
    rw [← Set.Nat.card_coe_set_eq]
    calc
      Nat.card H = Nat.card (Fin (m+1)) := Nat.card_range_of_injective hf
      _ = m+1 := by simp
  apply Nat.le_of_not_gt
  intro hlarge
  obtain ⟨q,hq,hdegree⟩ := Sensitivity.huang_degree_theorem H (by
    rw [← Set.ncard_eq_toFinset_card']
    omega)
  rcases hq with ⟨i,rfl⟩
  have hsmall := snake_degree_le_two p i
  change (H ∩ (f i).adjacent).toFinset.card ≤ 2 at hsmall
  norm_num at hdegree
  rw [Set.toFinset_inter] at hsmall
  omega

theorem verified_bounds : Nonempty (Snake 191) ∧
    (∀ m, Nonempty (Snake m) → m ≤ 255) := by
  refine ⟨lower_bound,?_⟩
  rintro m ⟨p⟩
  exact universal_upper_bound_255 p

#print axioms universal_upper_bound_255
#print axioms verified_bounds
end
end Snake9
