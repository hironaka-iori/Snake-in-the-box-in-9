import OutsideCount136
import PairRepresentation134

namespace Snake9.ActualInterval137
open Snake9.LocalWindow

set_option maxHeartbeats 1000000

theorem exists_coordinate_list {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (q a lo hi : Nat) (ha : a < 9) (haq : a ≠ q)
    (hzero : vx p 0 = 0) (hfirst : vx p 1 = 2^q)
    (hbound : lo ≤ hi) (hfit : 2*(hi+3) ≤ m)
    (hcover : ∀ z, lo ≤ z → z ≤ hi+3 → vx p (2*z) ∈ nbrs (2^a)) :
    ∃ L : List Nat,
      L.length = hi+4-max lo 2 ∧
      (∀ b ∈ L, b < 9 ∧ b ≠ a ∧ b ≠ q) ∧
      (∀ i, i < L.length → 2*(max lo 2)+2*i ≤ m) ∧
      (∀ i, i < L.length → vx p (2*(max lo 2)+2*i) =
        2^a ^^^ 2^(L.getD i 0)) := by
  classical
  let n := hi+4-max lo 2
  have hex (i : Fin n) : ∃ b, b < 9 ∧ b ≠ a ∧ b ≠ q ∧
      vx p (2*(max lo 2)+2*i.val) = 2^a ^^^ 2^b := by
    have hiN : i.val < hi+4-max lo 2 := i.isLt
    have hlow : lo ≤ max lo 2 + i.val := by omega
    have hupp : max lo 2 + i.val ≤ hi+3 := by omega
    have hindex : 2*(max lo 2)+2*i.val = 2*(max lo 2+i.val) := by omega
    have hj : 2*(max lo 2)+2*i.val ≤ m := by omega
    have hadj : vx p (2*(max lo 2)+2*i.val) ∈ nbrs (2^a) := by
      rw [hindex]
      exact hcover _ hlow hupp
    rcases PairRepresentation134.selected_neighbour_pairs p hm q a _ ha haq
      hzero hfirst hj hadj with hz | ht | hb
    · omega
    · omega
    · exact hb
  choose c hc using hex
  let L := List.ofFn c
  have hlength : L.length = n := List.length_ofFn
  refine ⟨L,hlength,?_,?_,?_⟩
  · intro b hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    exact ⟨(hc i).1,(hc i).2.1,(hc i).2.2.1⟩
  · intro i hiL
    have hiN : i < hi+4-max lo 2 := by simpa only [hlength] using hiL
    omega
  · intro i hiL
    have hiN : i < n := by simpa only [hlength] using hiL
    have hget : L.getD i 0 = c ⟨i,hiN⟩ := by
      simp only [L,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
        dif_pos hiN,Option.getD_some]
    rw [hget]
    exact (hc ⟨i,hiN⟩).2.2.2

theorem regular_interval_bound {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (q a lo hi : Nat) (A : Finset Nat)
    (hq : q < 9) (ha : a ∈ A) (hA : A ⊆ (Finset.range 9).erase q)
    (hzero : vx p 0 = 0) (hfirst : vx p 1 = 2^q)
    (hbound : lo ≤ hi) (hfit : 2*(hi+3) ≤ m)
    (hcover : ∀ z, lo ≤ z → z ≤ hi+3 → vx p (2*z) ∈ nbrs (2^a)) :
    let C := (Finset.range 9).erase q
    let F := (C.powersetCard 2).filter (fun e => (e ∩ A).Nonempty ∧
      ∀ b ∈ e, ∀ c ∈ e, b ≠ c → sel p (fun v => v) (2^b ^^^ 2^c) = false)
    hi+4-max lo 2 ≤
      max 1 (8-A.card-(F.filter (fun e => a ∈ e ∧ ¬ e ⊆ A)).card) +
        (F.card-(F.filter (fun e => a ∈ e)).card) ∧
    hi+4-max lo 2 + (F.filter (fun e => a ∈ e)).card ≤
      max 1 (8-A.card-(F.filter (fun e => a ∈ e ∧ ¬ e ⊆ A)).card) + F.card := by
  classical
  dsimp only
  let C := (Finset.range 9).erase q
  let U := C.filter (fun b => b ≠ a ∧ sel p (fun v => v) (2^a ^^^ 2^b) = true)
  let F := (C.powersetCard 2).filter (fun e => (e ∩ A).Nonempty ∧
    ∀ b ∈ e, ∀ c ∈ e, b ≠ c → sel p (fun v => v) (2^b ^^^ 2^c) = false)
  change hi+4-max lo 2 ≤
      max 1 (8-A.card-(F.filter (fun e => a ∈ e ∧ ¬ e ⊆ A)).card) +
        (F.card-(F.filter (fun e => a ∈ e)).card) ∧
    hi+4-max lo 2 + (F.filter (fun e => a ∈ e)).card ≤
      max 1 (8-A.card-(F.filter (fun e => a ∈ e ∧ ¬ e ⊆ A)).card) + F.card
  have haC := Finset.mem_erase.mp (hA ha)
  have ha9 := Finset.mem_range.mp haC.2
  obtain ⟨L,hlen,hcoords,hfits,hvalues⟩ :=
    exists_coordinate_list p hm q a lo hi ha9 haC.1 hzero hfirst hbound hfit hcover
  have hrun := ActualMissingSets136.length_le_actual_missing_pairs
    p (2*(max lo 2)) a q L A hq ha hA (by omega) hzero hcoords hfits hvalues
  have hrun' : L.length ≤ max 1 ((U \ A).card) +
      (F.card-(F.filter (fun e => a ∈ e)).card) := hrun.2.1
  have hout : (U \ A).card +
      (F.filter (fun e => a ∈ e ∧ ¬ e ⊆ A)).card = 8-A.card :=
    OutsideCount136.outside_card_add_crossing_degree p a q A hq ha hA
  have heq : (U \ A).card =
      8-A.card-(F.filter (fun e => a ∈ e ∧ ¬ e ⊆ A)).card := by omega
  rw [heq,hlen] at hrun'
  have hdegree : (F.filter (fun e => a ∈ e)).card ≤ F.card := Finset.card_filter_le _ _
  exact ⟨hrun',by omega⟩

#print axioms exists_coordinate_list
#print axioms regular_interval_bound
end Snake9.ActualInterval137
