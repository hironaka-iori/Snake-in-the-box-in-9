import Mathlib.Tactic
import LocalWindowShareBridge
import LocalWindowDirBridge

namespace Snake9.LocalWindow.ForcedShare58
set_option maxHeartbeats 0

theorem count_mono {α : Type} (S U : α → Bool) (l : List α)
    (h : ∀ x ∈ l, S x = true → U x = true) :
    (l.filter S).length ≤ (l.filter U).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ht := ih (fun x hx => h x (by simp [hx]))
    have ha := h a (by simp)
    cases hs : S a <;> cases hu : U a <;>
      simp_all [List.filter_cons] <;> omega

def forceCheck (W D : List Nat) : Bool :=
  D.all fun q => W.any fun v => decide (3 ≤ cnt (fun t => (q::W).contains t) (nbrs v))

def supportCheck (W C : List Nat) : Bool :=
  C.all fun x => (List.range 9).all fun k =>
    decide (0 < cnt (fun t => W.contains t) (nbrs (x ^^^ (1 <<< k))))

theorem forced_absent (S : Nat → Bool) (W D : List Nat)
    (hW : ∀ v ∈ W, S v = true)
    (hd : ∀ v, S v = true → cnt S (nbrs v) ≤ 2)
    (hc : forceCheck W D = true) : ∀ q ∈ D, S q = false := by
  intro q hq
  have h := List.all_eq_true.mp hc q hq
  obtain ⟨v,hv,hv3⟩ := List.any_eq_true.mp h
  have hv3' : 3 ≤ cnt (fun t => (q::W).contains t) (nbrs v) := of_decide_eq_true hv3
  cases he : S q with
  | false => rfl
  | true =>
    have hm := count_mono (fun t => (q::W).contains t) S (nbrs v) (by
      intro x _ hx
      have hx' : x ∈ q::W := List.contains_iff.mp hx
      rcases List.mem_cons.mp hx' with h | h
      · simpa [h] using he
      · exact hW x h)
    have hh := hd v (hW v hv)
    change cnt (fun t => (q::W).contains t) (nbrs v) ≤ cnt S (nbrs v) at hm
    omega

theorem empty_mono (S U : Nat → Bool) (q : Nat)
    (h : ∀ x, S x = true → U x = true) : emptyCount U q ≤ emptyCount S q := by
  apply count_mono
  intro ab _ he
  rw [emptyPred_iff] at he ⊢
  have hf : ∀ x, U x = false → S x = false := by
    intro x hx
    cases hs : S x
    · rfl
    · have := h x hs; simp_all
  exact ⟨hf _ he.1,hf _ he.2.1,hf _ he.2.2.1,hf _ he.2.2.2⟩

theorem local_share_mono (M : Nat) (S U : Nat → Bool) (x : Nat)
    (h : ∀ y, S y = true → U y = true)
    (hp : ∀ k ∈ List.range 9, 0 < cnt S (nbrs (x ^^^ (1 <<< k)))) :
    shareLocal M U x ≤ shareLocal M S x := by
  apply List.sum_le_sum
  intro k hk
  have hd := count_mono S U (nbrs (x ^^^ (1 <<< k))) (fun y _ => h y)
  have he := empty_mono S U (x ^^^ (1 <<< k)) h
  have hn := Nat.mul_le_mul_left M he
  change cnt S (nbrs (x ^^^ (1 <<< k))) ≤ cnt U (nbrs (x ^^^ (1 <<< k))) at hd
  exact (Nat.div_le_div_right hn).trans (Nat.div_le_div_left hd (hp k hk))

theorem forced_share (M : Nat) (S : Nat → Bool) (W D C : List Nat)
    (hW : ∀ v ∈ W, S v = true)
    (hd : ∀ v, S v = true → cnt S (nbrs v) ≤ 2)
    (hf : forceCheck W D = true) (hp : supportCheck W C = true) :
    (C.map (shareLocal M (fun x => !D.contains x))).sum ≤
      (C.map (shareLocal M S)).sum := by
  have ha := forced_absent S W D hW hd hf
  have hU : ∀ x, S x = true → (!D.contains x) = true := by
    intro x hx
    cases hc : D.contains x
    · simp [hc]
    · have := ha x (List.contains_iff.mp hc); simp_all
  apply List.sum_le_sum
  intro x hx
  apply local_share_mono M S _ x hU
  intro k hk
  have h := List.all_eq_true.mp (List.all_eq_true.mp hp x hx) k hk
  have h' : 0 < cnt (fun t => W.contains t) (nbrs (x ^^^ (1 <<< k))) := of_decide_eq_true h
  have hc := count_mono (fun t => W.contains t) S (nbrs (x ^^^ (1 <<< k))) (by
    intro t _ ht
    exact hW t (List.contains_iff.mp ht))
  change cnt (fun t => W.contains t) (nbrs (x ^^^ (1 <<< k))) ≤ cnt S (nbrs (x ^^^ (1 <<< k))) at hc
  omega

#print axioms forced_absent
#print axioms empty_mono
#print axioms local_share_mono
#print axioms forced_share
end Snake9.LocalWindow.ForcedShare58
