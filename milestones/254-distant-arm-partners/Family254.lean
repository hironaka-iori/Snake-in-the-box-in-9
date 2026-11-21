import LayerJoining

namespace Family254
open LayerJoining

variable {V : Type}

def Avoids (used forbidden : V → Prop) : Prop := ∀ v, forbidden v → ¬ used v

def Obstacle (common : V → Prop) (a b : Bool → V) (i j : Bool) (v : V) : Prop :=
  common v ∨ v = a i ∨ v = b j

private theorem omits_one (used : V → Prop) (points : Bool → V) :
    (∃ i, ¬ used (points i)) ↔ ¬ (used (points false) ∧ used (points true)) := by
  constructor
  · rintro ⟨i, hi⟩ both
    cases i with
    | false => exact hi both.1
    | true => exact hi both.2
  · intro h
    by_cases first : used (points false)
    · exact ⟨true, fun second => h ⟨first, second⟩⟩
    · exact ⟨false, first⟩

/-- Each parent forbids the common vertices and one vertex from each pair. -/
theorem four_choices_iff (used common : V → Prop) (a b : Bool → V) :
    (∃ i j, Avoids used (Obstacle common a b i j)) ↔
      Avoids used common ∧ ¬ (used (a false) ∧ used (a true)) ∧
        ¬ (used (b false) ∧ used (b true)) := by
  constructor
  · rintro ⟨i, j, avoids⟩
    exact ⟨fun v hv => avoids v (.inl hv),
           (omits_one used a).mp ⟨i, avoids _ (.inr (.inl rfl))⟩,
           (omits_one used b).mp ⟨j, avoids _ (.inr (.inr rfl))⟩⟩
  · rintro ⟨commonFree, ha, hb⟩
    obtain ⟨i, hi⟩ := (omits_one used a).mpr ha
    obtain ⟨j, hj⟩ := (omits_one used b).mpr hb
    refine ⟨i, j, ?_⟩
    rintro v (hc | hv | hv)
    · exact commonFree v hc
    · simpa only [hv] using hi
    · simpa only [hv] using hj

variable {R : V → V → Prop} {m n : Nat}

def Used (q : InducedPath V R n) (v : V) : Prop := ∃ k, q.vertex k = v

/-- Parents end at the partner's first vertex. Their vertices strictly before
the crossing are exactly the recorded obstacles. -/
theorem rooted_family_iff (p : Bool → Bool → InducedPath V R m) (q : InducedPath V R n)
    (common : V → Prop) (a b : Bool → V)
    (root : ∀ i j, (p i j).vertex (Fin.last m) = q.vertex 0)
    (sites : ∀ i j v, (∃ k : Fin (m+1), k.val < m ∧ (p i j).vertex k = v) ↔
      Obstacle common a b i j v) :
    (∃ i j, Compatible (p i j) q) ↔
      Avoids (Used q) common ∧ ¬ (Used q (a false) ∧ Used q (a true)) ∧
        ¬ (Used q (b false) ∧ Used q (b true)) := by
  rw [← four_choices_iff]
  constructor
  · rintro ⟨i, j, fits⟩
    refine ⟨i, j, ?_⟩
    rintro v hv ⟨t, he⟩
    obtain ⟨k, hk, eq⟩ := (sites i j v).mpr hv
    exact (Nat.ne_of_lt hk) ((fits k t).mp (eq.trans he.symm)).1
  · rintro ⟨i, j, avoids⟩
    refine ⟨i, j, ?_⟩
    intro k t
    constructor
    · intro eq
      have last : k.val = m := by
        by_cases hk : k.val < m
        · exact False.elim (avoids _ ((sites i j _).mp ⟨k, hk, rfl⟩) ⟨t, eq.symm⟩)
        · have := k.isLt
          omega
      have hk : k = Fin.last m := Fin.ext last
      have base : (p i j).vertex k = q.vertex 0 := by simpa only [hk] using root i j
      have ht : t = 0 := q.distinct t 0 (eq.symm.trans base)
      exact ⟨last, congrArg Fin.val ht⟩
    · rintro ⟨hk, ht⟩
      have ek : k = Fin.last m := Fin.ext hk
      have et : t = 0 := Fin.ext ht
      subst k
      subst t
      exact root i j

#print axioms four_choices_iff
#print axioms rooted_family_iff

end Family254
