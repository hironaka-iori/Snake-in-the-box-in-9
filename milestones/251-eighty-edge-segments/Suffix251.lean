import FreedSite250

namespace Suffix251
open FreedSite250

variable {V : Type} {R : V → V → Prop} {w : Nat → V} {n : Nat}

/-- Any contiguous segment of an indexed induced path is induced. -/
theorem induced_segment (path : InducedThrough R w n) {t k : Nat} (bound : t + k ≤ n) :
    InducedThrough R (fun i => w (t + i)) k := by
  intro i j hij hj
  have pair := path (t + i) (t + j) (by omega) (by omega)
  exact ⟨pair.1, pair.2.trans (show (t + i + 1 = t + j) ↔ i + 1 = j by omega)⟩

/-- After the cut, each future vertex avoids the closed neighbourhood of
each strictly earlier vertex. The vertex at the cut itself is exempt. -/
theorem suffix_avoids_prior_neighbourhoods (path : InducedThrough R w n)
    {t j : Nat} (afterCut : t < j) (hj : j ≤ n) :
    ¬ ∃ i, i < t ∧ (w i = w j ∨ R (w i) (w j)) := by
  rintro ⟨i, hi, incident⟩
  have pair := path i j (by omega) hj
  rcases incident with eq | adj
  · exact pair.1 eq
  · have step := pair.2.mp adj
    omega

/-- The old bound is at the shifted root w(t). Its occupied sites outside
the current parent and the shifted root are contained in the exceptional set.
A suffix longer than the old cap must enter this set by step t+cap+1. -/
theorem suffix_forced_hit {root : V} {oldParent newParent exceptional : V → Prop}
    {t cap : Nat} (path : InducedThrough R w n) (fitsNew : Fits root newParent w n)
    (oldCap : RootedCap R (w t) oldParent cap)
    (missing : ∀ v, oldParent v → ¬ newParent v → v ≠ w t → exceptional v)
    (long : t + cap < n) :
    ∃ j, t < j ∧ j ≤ t + cap + 1 ∧ exceptional (w j) := by
  apply Classical.byContradiction
  intro absent
  have bound : t + (cap + 1) ≤ n := by omega
  have fitsOld : Fits (w t) oldParent (fun i => w (t + i)) (cap + 1) := by
    refine ⟨by simp, ?_⟩
    intro i hi hprefix hold
    have absIndex : t + i ≤ n := by omega
    have distinct := (path t (t + i) (by omega) absIndex).1
    have exceptionalSite := missing (w (t + i)) hold
      (fitsNew.2 (t + i) (by omega) absIndex) (fun eq => distinct eq.symm)
    exact absent ⟨t + i, by omega, by omega, exceptionalSite⟩
  have impossible := oldCap (fun i => w (t + i)) (cap + 1) (induced_segment path bound) fitsOld
  omega

/-- If every exceptional site is already blocked at the cut, the whole
partner has length at most t+cap. -/
theorem suffix_bound_of_blocked {root : V} {oldParent newParent exceptional : V → Prop}
    {t cap : Nat} (path : InducedThrough R w n) (fitsNew : Fits root newParent w n)
    (oldCap : RootedCap R (w t) oldParent cap)
    (missing : ∀ v, oldParent v → ¬ newParent v → v ≠ w t → exceptional v)
    (blocked : ∀ v, exceptional v → ∃ i, i < t ∧ (w i = v ∨ R (w i) v)) :
    n ≤ t + cap := by
  apply Nat.le_of_not_gt
  intro long
  obtain ⟨j, hj, deadline, hit⟩ := suffix_forced_hit path fitsNew oldCap missing long
  exact suffix_avoids_prior_neighbourhoods path hj (by omega) (blocked (w j) hit)

#print axioms induced_segment
#print axioms suffix_avoids_prior_neighbourhoods
#print axioms suffix_forced_hit
#print axioms suffix_bound_of_blocked

end Suffix251
