import Std

namespace FreedSite250

variable {V : Type} {R : V → V → Prop}

/-- The word on indices 0 through n is a simple induced path of n edges. -/
def InducedThrough (R : V → V → Prop) (w : Nat → V) (n : Nat) : Prop :=
  ∀ i j, i < j → j ≤ n →
    w i ≠ w j ∧ (R (w i) (w j) ↔ i + 1 = j)

/-- The partner starts at the joining root. All positive-index vertices avoid the parent. -/
def Fits (root : V) (parent : V → Prop) (w : Nat → V) (n : Nat) : Prop :=
  w 0 = root ∧ ∀ i, 0 < i → i ≤ n → ¬ parent (w i)

/-- The old parent cap is an input about all compatible rooted induced paths. -/
def RootedCap (R : V → V → Prop) (root : V) (parent : V → Prop) (cap : Nat) : Prop :=
  ∀ (w : Nat → V) (n : Nat), InducedThrough R w n → Fits root parent w n → n ≤ cap

/-- A compatible partner exceeding the old cap must visit the single freed site
within its first cap+1 edges. Only containment of the removed set is needed. -/
theorem forced_hit {root freed : V} {oldParent newParent : V → Prop}
    {w : Nat → V} {n cap : Nat}
    (oldCap : RootedCap R root oldParent cap)
    (onlyFreed : ∀ v, oldParent v → ¬ newParent v → v = freed)
    (path : InducedThrough R w n) (fitsNew : Fits root newParent w n) (long : cap < n) :
    ∃ i, 0 < i ∧ i ≤ cap + 1 ∧ w i = freed := by
  apply Classical.byContradiction
  intro absent
  have prefixPath : InducedThrough R w (cap + 1) :=
    fun i j hij hj => path i j hij (by omega)
  have fitsOld : Fits root oldParent w (cap + 1) := by
    refine ⟨fitsNew.1, ?_⟩
    intro i hi hprefix hold
    have eq := onlyFreed (w i) hold (fitsNew.2 i hi (by omega))
    exact absent ⟨i, hi, hprefix, eq⟩
  have impossible := oldCap w (cap + 1) prefixPath fitsOld
  omega

/-- With an additional edge after this prefix, the visit has both a predecessor
and a successor in the full partner. Equality n = cap+1 permits an endpoint hit. -/
theorem forced_internal_hit {root freed : V} {oldParent newParent : V → Prop}
    {w : Nat → V} {n cap : Nat}
    (oldCap : RootedCap R root oldParent cap)
    (onlyFreed : ∀ v, oldParent v → ¬ newParent v → v = freed)
    (path : InducedThrough R w n) (fitsNew : Fits root newParent w n) (long : cap + 1 < n) :
    ∃ i, 0 < i ∧ i ≤ cap + 1 ∧ i < n ∧ w i = freed := by
  obtain ⟨i, hi, hprefix, eq⟩ := forced_hit oldCap onlyFreed path fitsNew (by omega)
  exact ⟨i, hi, hprefix, by omega, eq⟩

#print axioms forced_hit
#print axioms forced_internal_hit

end FreedSite250
