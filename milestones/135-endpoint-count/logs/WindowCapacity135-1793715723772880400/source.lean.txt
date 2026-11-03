import PairRepresentation134
import PairCapacity134
import Mathlib.Tactic

namespace Snake9.WindowCapacity135
open Snake9.LocalWindow

theorem covered_positions_card_le {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (q : Fin 9) (I : Finset Nat) (f : Nat → Fin 9)
    (hzero : vx p 0 = 0) (hfirst : vx p 1 = 2^q.val)
    (hlabels : ∀ r, r ∈ I → f r ≠ q)
    (hfit : ∀ r, r ∈ I → 2*r+6 ≤ m)
    (hfour : ∀ r, r ∈ I → ∀ j, j < 4 →
      vx p (2*r+2*j) ∈ nbrs (2^(f r).val)) :
    (I.biUnion (fun r => Finset.Icc r (r+3))).card ≤
      7*(I.image f).card - (I.image f).card*((I.image f).card-1)/2 + 2 := by
  classical
  let A := I.image f
  let W := I.biUnion (fun r => Finset.Icc r (r+3))
  let T := W \ ({0,1} : Finset Nat)
  let B := (Finset.univ : Finset (Fin 9 × Fin 9)).filter (fun ab =>
    ab.1 < ab.2 ∧ ab.1 ≠ q ∧ ab.2 ≠ q ∧ (ab.1 ∈ A ∨ ab.2 ∈ A))
  have hq : q ∉ A := by
    intro hqA
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hqA
    exact hlabels r hr he
  have hcover (t : Nat) (ht : t ∈ W) :
      ∃ r, r ∈ I ∧ r ≤ t ∧ t ≤ r+3 := by
    obtain ⟨r,hr,htr⟩ := Finset.mem_biUnion.mp ht
    exact ⟨r,hr,(Finset.mem_Icc.mp htr).1,(Finset.mem_Icc.mp htr).2⟩
  have hbound (t : Nat) (ht : t ∈ W) : 2*t ≤ m := by
    obtain ⟨r,hr,hrt,htr⟩ := hcover t ht
    have hf := hfit r hr
    omega
  have hsub : T.image (fun t => vx p (2*t)) ⊆
      B.image (fun ab => 2^ab.1.val ^^^ 2^ab.2.val) := by
    intro v hv
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨htW,htnot⟩ := Finset.mem_sdiff.mp ht
    have ht0 : t ≠ 0 := by
      intro he
      exact htnot (by simp [he])
    have ht1 : t ≠ 1 := by
      intro he
      exact htnot (by simp [he])
    obtain ⟨r,hr,hrt,htr⟩ := hcover t htW
    have hadj : vx p (2*t) ∈ nbrs (2^(f r).val) := by
      have hf := hfour r hr (t-r) (by omega)
      have he : 2*r+2*(t-r) = 2*t := by omega
      simpa only [he] using hf
    have hfrq : (f r).val ≠ q.val := by
      intro he
      exact hlabels r hr (Fin.ext he)
    have hp := PairRepresentation134.selected_neighbour_pairs p hm
      q.val (f r).val (2*t) (f r).isLt hfrq hzero hfirst (hbound t htW) hadj
    rcases hp with hz | ht | ⟨b,hb,hba,hbq,hv⟩
    · exact False.elim (ht0 (by omega))
    · exact False.elim (ht1 (by omega))
    · let b' : Fin 9 := ⟨b,hb⟩
      have hb'q : b' ≠ q := by
        intro he
        exact hbq (congrArg Fin.val he)
      have hfrA : f r ∈ A := Finset.mem_image.mpr ⟨r,hr,rfl⟩
      apply Finset.mem_image.mpr
      by_cases hab : (f r).val < b
      · refine ⟨(f r,b'),?_,?_⟩
        · apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _,hab,hlabels r hr,hb'q,Or.inl hfrA⟩
        · exact hv.symm
      · have hba' : b < (f r).val := by omega
        refine ⟨(b',f r),?_,?_⟩
        · apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _,hba',hb'q,hlabels r hr,Or.inr hfrA⟩
        · change 2^b ^^^ 2^(f r).val = vx p (2*t)
          rw [Nat.xor_comm]
          exact hv.symm
  have hinj : Set.InjOn (fun t => vx p (2*t)) T := by
    intro t ht s hs he
    have htW := (Finset.mem_sdiff.mp ht).1
    have hsW := (Finset.mem_sdiff.mp hs).1
    have hi := vx_inj p (hbound t htW) (hbound s hsW) he
    omega
  have hT : T.card ≤ 7*A.card - A.card*(A.card-1)/2 := by
    calc
      T.card = (T.image (fun t => vx p (2*t))).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (B.image (fun ab => 2^ab.1.val ^^^ 2^ab.2.val)).card :=
        Finset.card_le_card hsub
      _ ≤ B.card := Finset.card_image_le
      _ = 7*A.card - A.card*(A.card-1)/2 :=
        PairCapacity134.incident_pair_card q A hq
  have hsplit := Finset.card_sdiff_add_card_inter W ({0,1} : Finset Nat)
  have hex : (W ∩ ({0,1} : Finset Nat)).card ≤ 2 := by
    calc
      (W ∩ ({0,1} : Finset Nat)).card ≤ ({0,1} : Finset Nat).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = 2 := by decide
  change W.card ≤ 7*A.card - A.card*(A.card-1)/2 + 2
  change T.card + (W ∩ ({0,1} : Finset Nat)).card = W.card at hsplit
  omega

#print axioms covered_positions_card_le
end Snake9.WindowCapacity135
