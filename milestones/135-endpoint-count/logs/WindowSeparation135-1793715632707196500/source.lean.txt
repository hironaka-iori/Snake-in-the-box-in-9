import LocalWindowBridge
import Mathlib.Data.Finset.Card

namespace Snake9.WindowSeparation135
open Snake9.LocalWindow

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

private theorem common_unit_flip_cases : ∀ a b c d : Fin 9, a ≠ b →
    (2^a.val ^^^ 2^c.val) = (2^b.val ^^^ 2^d.val) → c=a ∨ c=b := by
  decide

theorem common_unit_neighbors (a b w : Nat) (ha : a < 9) (hb : b < 9)
    (hab : a ≠ b) (hwa : w ∈ nbrs (2^a)) (hwb : w ∈ nbrs (2^b)) :
    w=0 ∨ w=2^a ^^^ 2^b := by
  obtain ⟨c,hc,hec⟩ := (mem_nbrs _ _).mp hwa
  obtain ⟨d,hd,hed⟩ := (mem_nbrs _ _).mp hwb
  have hab' : (⟨a,ha⟩ : Fin 9) ≠ ⟨b,hb⟩ := by
    intro he
    exact hab (congrArg Fin.val he)
  rcases common_unit_flip_cases ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ ⟨d,hd⟩ hab'
      (hec.symm.trans hed) with hca | hcb
  · left
    have hca' : c=a := congrArg Fin.val hca
    rw [hec,hca',Nat.xor_self]
  · right
    have hcb' : c=b := congrArg Fin.val hcb
    rw [hec,hcb']

theorem selected_common_unit_pair {m : Nat} (p : Snake m) (i a b : Nat)
    (hi : i ≤ m) (hi0 : 0 < i) (hzero : vx p 0 = 0)
    (ha : a < 9) (hb : b < 9) (hab : a ≠ b)
    (hwa : vx p i ∈ nbrs (2^a)) (hwb : vx p i ∈ nbrs (2^b)) :
    vx p i = 2^a ^^^ 2^b := by
  rcases common_unit_neighbors a b (vx p i) ha hb hab hwa hwb with h0 | hp
  · have hi' := vx_inj p hi (show 0 ≤ m by omega) (h0.trans hzero.symm)
    omega
  · exact hp

theorem different_labels_separated {m : Nat} (p : Snake m) (u v a b : Nat)
    (hzero : vx p 0 = 0) (hfit : 2*u+6 ≤ m)
    (ha : a < 9) (hb : b < 9) (hab : a ≠ b) (huv : u < v)
    (hleft : ∀ j, j < 4 → vx p (2*u+2*j) ∈ nbrs (2^a))
    (hright : ∀ j, j < 4 → vx p (2*v+2*j) ∈ nbrs (2^b)) :
    u+3 ≤ v := by
  by_contra hn
  have hvu : v ≤ u+2 := by omega
  have hleft2 : vx p (2*u+4) ∈ nbrs (2^a) := by simpa using hleft 2 (by decide)
  have hleft3 : vx p (2*u+6) ∈ nbrs (2^a) := by simpa using hleft 3 (by decide)
  have hright2 : vx p (2*u+4) ∈ nbrs (2^b) := by
    have hh := hright (u+2-v) (by omega)
    have he : 2*v+2*(u+2-v) = 2*u+4 := by omega
    rw [he] at hh
    exact hh
  have hright3 : vx p (2*u+6) ∈ nbrs (2^b) := by
    have hh := hright (u+3-v) (by omega)
    have he : 2*v+2*(u+3-v) = 2*u+6 := by omega
    rw [he] at hh
    exact hh
  have hpair2 := selected_common_unit_pair p (2*u+4) a b
    (by omega) (by omega) hzero ha hb hab hleft2 hright2
  have hpair3 := selected_common_unit_pair p (2*u+6) a b
    hfit (by omega) hzero ha hb hab hleft3 hright3
  have he := vx_inj p (show 2*u+4 ≤ m by omega) hfit (hpair2.trans hpair3.symm)
  omega

theorem sampled_window_separation {m : Nat} (p : Snake m) (I : Finset Nat)
    (label : Nat → Nat) (hzero : vx p 0 = 0)
    (hfit : ∀ t ∈ I, 2*t+6 ≤ m)
    (hcoord : ∀ t ∈ I, label t < 9)
    (hwindow : ∀ t ∈ I, ∀ j, j < 4 → vx p (2*t+2*j) ∈ nbrs (2^(label t))) :
    ∀ u ∈ I, ∀ v ∈ I, u < v → label u ≠ label v → u+3 ≤ v := by
  intro u hu v hv huv hlabels
  exact different_labels_separated p u v (label u) (label v) hzero (hfit u hu)
    (hcoord u hu) (hcoord v hv) hlabels huv (hwindow u hu) (hwindow v hv)

#print axioms common_unit_neighbors
#print axioms selected_common_unit_pair
#print axioms different_labels_separated
#print axioms sampled_window_separation
end Snake9.WindowSeparation135
