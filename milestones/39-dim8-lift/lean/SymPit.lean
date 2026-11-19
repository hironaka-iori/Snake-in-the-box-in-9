import Sym
/-! Transport of a `Pit` along one generator of Aut(Q8). -/
set_option linter.deprecated false
namespace Dim8Lift.Sym
open Dim8Lift Dim8Lift.Cube

variable {c : Nat}

theorem sm_perm (hc : c < 36) (F : Nat → Nat) : sm 256 (fun u => F (gen c u)) = sm 256 F := by
  have := sm_reindex 256 256 (fun _ => true) (gen c) F (fun t ht _ => gen_lt hc ht) (by
    intro u hu
    have h1 : cnt 256 (fun t => true && gen c t == u) ≤ 1 := by
      apply cnt_le_one; intro t t' ht ht' p p'
      simp only [Bool.true_and, beq_iff_eq] at p p'
      rw [← gen_gen hc ht, ← gen_gen hc ht', p, p']
    have h2 : 1 ≤ cnt 256 (fun t => true && gen c t == u) :=
      cnt_pos (t := gen c u) (gen_lt hc hu) (by simp [gen_gen hc hu])
    rw [show cnt 256 (fun t => true && gen c t == u) = 1 by omega]; simp)
  rw [this]; apply sm_congr; intro t _; simp

theorem twoB_gen (hc : c < 36) (S : Nat → Bool) {u : Nat} (hu : u < 256) :
    twoB (fun v => S (gen c v)) u = twoB S (gen c u) := by
  apply Bool.eq_iff_iff.mpr; rw [twoB_iff, twoB_iff]
  constructor
  · rintro ⟨a, b, hab, hb, h1, h2⟩
    rw [gen_nb hc hu (by omega)] at h1; rw [gen_nb hc hu hb] at h2
    have ne : dmap c a ≠ dmap c b := by
      intro e; have := congrArg (dmap c) e; rw [dmap_dmap hc (by omega), dmap_dmap hc hb] at this; omega
    rcases Nat.lt_or_gt_of_ne ne with h | h
    · exact ⟨_, _, h, dmap_lt hc hb, h1, h2⟩
    · exact ⟨_, _, h, dmap_lt hc (by omega), h2, h1⟩
  · rintro ⟨a, b, hab, hb, h1, h2⟩
    have e1 : gen c (nb u (dmap c a)) = nb (gen c u) a := by rw [gen_nb hc hu (dmap_lt hc (by omega)), dmap_dmap hc (by omega)]
    have e2 : gen c (nb u (dmap c b)) = nb (gen c u) b := by rw [gen_nb hc hu (dmap_lt hc hb), dmap_dmap hc hb]
    have ne : dmap c a ≠ dmap c b := by
      intro e; have := congrArg (dmap c) e; rw [dmap_dmap hc (by omega), dmap_dmap hc hb] at this; omega
    rcases Nat.lt_or_gt_of_ne ne with h | h
    · exact ⟨_, _, h, dmap_lt hc hb, by simp only [e1]; exact h1, by simp only [e2]; exact h2⟩
    · exact ⟨_, _, h, dmap_lt hc (by omega), by simp only [e2]; exact h2, by simp only [e1]; exact h1⟩

theorem anyB_gen (hc : c < 36) (S : Nat → Bool) {u : Nat} (hu : u < 256) :
    anyB (fun v => S (gen c v)) u = anyB S (gen c u) := by
  apply Bool.eq_iff_iff.mpr; rw [anyB_iff, anyB_iff]
  constructor
  · rintro ⟨a, ha, h1⟩
    rw [gen_nb hc hu ha] at h1; exact ⟨_, dmap_lt hc ha, h1⟩
  · rintro ⟨a, ha, h1⟩
    refine ⟨dmap c a, dmap_lt hc ha, ?_⟩
    show S (gen c (nb u (dmap c a))) = true
    rw [gen_nb hc hu (dmap_lt hc ha), dmap_dmap hc ha]; exact h1

theorem pit_gen {c' L D : Nat} (hc : c < 36) {S : Nat → Bool} {ℓ : Nat → Nat} (hp : Pit c' L D S ℓ) :
    Pit c' L D (fun u => S (gen c u)) (fun u => ℓ (gen c u)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u hu a b d hab hbd hd h0 h1 h2
    cases h3 : S (gen c (nb u d))
    · rfl
    · exfalso
      have hu' := gen_lt hc hu
      rw [gen_nb hc hu (by omega)] at h1; rw [gen_nb hc hu (by omega)] at h2; rw [gen_nb hc hu hd] at h3
      have inj : ∀ x y, x < 8 → y < 8 → x ≠ y → dmap c x ≠ dmap c y := by
        intro x y hx hy hxy e; have := congrArg (dmap c) e; rw [dmap_dmap hc hx, dmap_dmap hc hy] at this; exact hxy this
      exact deg3 hp hu' (dmap_lt hc (by omega)) (dmap_lt hc (by omega)) (dmap_lt hc hd)
        (inj a b (by omega) (by omega) (by omega)) (inj a d (by omega) hd (by omega)) (inj b d (by omega) hd (by omega))
        h0 h1 h2 h3
  · intro u hu; exact hp.lvl_le _ (gen_lt hc hu)
  · intro u hu h2
    rw [twoB_gen hc S hu] at h2
    obtain ⟨a', ha', hs, hl⟩ := hp.lvl _ (gen_lt hc hu) h2
    refine ⟨dmap c a', dmap_lt hc ha', ?_, ?_⟩
    · show S (gen c (nb u (dmap c a'))) = true
      rw [gen_nb hc hu (dmap_lt hc ha'), dmap_dmap hc ha']; exact hs
    · show ℓ (gen c (nb u (dmap c a'))) < ℓ (gen c u)
      rw [gen_nb hc hu (dmap_lt hc ha'), dmap_dmap hc ha']; exact hl
  · have : sm 256 (endW (fun v => S (gen c v))) = sm 256 (fun u => endW S (gen c u)) := by
      apply sm_congr; intro u hu
      unfold endW; rw [twoB_gen hc S hu, anyB_gen hc S hu]
    rw [this, sm_perm hc]; exact hp.ends
  · have : cnt 256 (fun v => S (gen c v)) = cnt 256 S := by
      unfold cnt; exact sm_perm hc (fun u => if S u then 1 else 0)
    rw [this]; exact hp.card

end Dim8Lift.Sym
