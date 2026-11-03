import DegreeSum137
import Numeric137

namespace Snake9.CountTwelve137

set_option maxHeartbeats 1000000

theorem count_le_twelve_from_blocks {α : Type*}
    (W : Nat) (B : List α) (label len : α → Nat)
    (A : Finset Nat) (F : Finset (Finset Nat))
    (hA : A = (B.map label).toFinset)
    (ha : 1 ≤ A.card) (ha8 : A.card ≤ 8)
    (hsize : ∀ e ∈ F, e.card = 2)
    (hmeet : ∀ e ∈ F, (e ∩ A).Nonempty)
    (hfirst : W+2*B.length+F.card ≤ 7*A.card-A.card*(A.card-1)/2+1)
    (hstarts : W+3*B.length ≤ (B.map len).sum+2)
    (hlen : ∀ b ∈ B, 2 ≤ len b)
    (hbound : ∀ b ∈ B, len b+(F.filter (fun e => label b ∈ e)).card ≤
      max 1 (8-A.card-(F.filter (fun e => label b ∈ e ∧ ¬ e ⊆ A)).card)+F.card) :
    W ≤ 12 := by
  classical
  have hak : A.card ≤ B.length := by
    have h := (B.map label).toFinset_card_le
    simpa only [← hA,List.length_map] using h
  by_contra hn
  have hlarge : 13 ≤ W := by omega
  by_cases ha7 : A.card ≤ 7
  · have hpoint : ∀ b ∈ B,
        len b+(F.filter (fun e => label b ∈ e)).card ≤ 8-A.card+F.card := by
      intro b hb
      have h := hbound b hb
      have hmax : max 1 (8-A.card-
          (F.filter (fun e => label b ∈ e ∧ ¬ e ⊆ A)).card) ≤ 8-A.card := by
        apply max_le <;> omega
      omega
    have hsum := DegreeSum137.sum_lengths_add_missing_card_le B label len A F
      hA hmeet hpoint
    have hsecond : W+3*B.length+F.card ≤ B.length*(8-A.card+F.card)+2 := by omega
    obtain ⟨ha5,hk5,ht3⟩ := Numeric137.exceptional_parameters
      W A.card B.length F.card ha ha7 hak hfirst hsecond hlarge
    have hexception : ∀ b ∈ B,
        len b+(F.filter (fun e => label b ∈ e)).card+
          (F.filter (fun e => label b ∈ e ∧ ¬ e ⊆ A)).card ≤
        6+(if (F.filter (fun e => label b ∈ e ∧ ¬ e ⊆ A)).card=3 then 1 else 0) := by
      intro b hb
      have h := hbound b hb
      have hs : (F.filter (fun e => label b ∈ e ∧ ¬ e ⊆ A)).card ≤ 3 := by
        have hh := Finset.card_filter_le F (fun e => label b ∈ e ∧ ¬ e ⊆ A)
        omega
      rw [ha5,ht3] at h
      norm_num at h
      split_ifs <;> omega
    have hsmall := DegreeSum137.exceptional_sum_lengths_le_twenty_five
      B label len A F hA hk5 ha5 ht3 hsize hmeet hexception
    omega
  · have haEq : A.card=8 := by omega
    have hfirst8 : W+2*B.length+F.card ≤ 29 := by
      simpa only [haEq] using hfirst
    obtain ⟨hk8,ht0⟩ := Numeric137.eight_coordinates W B.length F.card
      hfirst8 (by omega) hlarge
    have hB : B ≠ [] := by intro he; simp [he] at hk8
    obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil B hB
    have h := hbound b hb
    have hl := hlen b hb
    norm_num [haEq,ht0] at h
    omega

#print axioms count_le_twelve_from_blocks
end Snake9.CountTwelve137
