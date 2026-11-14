import LayerJoining
namespace FibreSymmetry204
open LayerJoining

def Adj {V W : Type} (R : V → V → Prop) (T : W → W → Prop) (x y : V × W) : Prop :=
  (x.1=y.1 ∧ T x.2 y.2) ∨ (R x.1 y.1 ∧ x.2=y.2)
def change {V W : Type} (g : V → W → W) (x : V × W) : V × W := (x.1,g x.1 x.2)

theorem injective {V W : Type} (g : V → W → W)
    (inj : ∀ z u v, g z u=g z v → u=v) (x y : V × W)
    (eq : change g x=change g y) : x=y := by
  rcases x with ⟨z,u⟩; rcases y with ⟨w,v⟩
  have base := congrArg Prod.fst eq
  change z=w at base; subst w
  have word := congrArg Prod.snd eq
  have same := inj z u v word
  subst v; rfl

theorem pairCriterion {V W : Type} (R : V → V → Prop) (T : W → W → Prop)
    (g : V → W → W) (inj : ∀ z u v, g z u=g z v → u=v)
    (iso : ∀ z u v, T (g z u) (g z v) ↔ T u v) (x y : V × W) :
    (Adj R T (change g x) (change g y) ↔ Adj R T x y) ↔
    (R x.1 y.1 → (g x.1 x.2=g y.1 y.2 ↔ x.2=y.2)) := by
  classical
  rcases x with ⟨z,u⟩; rcases y with ⟨w,v⟩
  by_cases same : z=w
  · subst w
    have eq : g z u=g z v ↔ u=v := ⟨inj z u v,congrArg (g z)⟩
    simp [Adj,change,iso,eq]
  · by_cases edge : R z w
    · simp [Adj,change,same,edge]
    · simp [Adj,change,same,edge]

theorem wholeSetCriterion {V W : Type} (R : V → V → Prop) (T : W → W → Prop)
    (g : V → W → W) (inj : ∀ z u v, g z u=g z v → u=v)
    (iso : ∀ z u v, T (g z u) (g z v) ↔ T u v) (S : V × W → Prop) :
    (∀ x y, S x → S y → (Adj R T (change g x) (change g y) ↔ Adj R T x y)) ↔
    (∀ x y, S x → S y → R x.1 y.1 → (g x.1 x.2=g y.1 y.2 ↔ x.2=y.2)) := by
  constructor
  · intro hs x y hx hy; exact (pairCriterion R T g inj iso x y).mp (hs x y hx hy)
  · intro hs x y hx hy; exact (pairCriterion R T g inj iso x y).mpr (hs x y hx hy)

def imagePath {V W : Type} {R : V → V → Prop} {T : W → W → Prop} {m : Nat}
    (p : InducedPath (V × W) (Adj R T) m)
    (g : V → W → W) (inj : ∀ z u v, g z u=g z v → u=v)
    (iso : ∀ z u v, T (g z u) (g z v) ↔ T u v)
    (compatible : ∀ i j, R (p.vertex i).1 (p.vertex j).1 →
      (g (p.vertex i).1 (p.vertex i).2=g (p.vertex j).1 (p.vertex j).2 ↔ (p.vertex i).2=(p.vertex j).2)) :
    InducedPath (V × W) (Adj R T) m where
  vertex i := change g (p.vertex i)
  distinct i j eq := p.distinct i j (injective g inj _ _ eq)
  induced i j hij := ((pairCriterion R T g inj iso _ _).mpr (compatible i j)).trans (p.induced i j hij)

theorem matchingSplit {W : Type} (A B : W → Prop) (r : W → W) :
    (∀ u v, A u → B v → (r u=v ↔ u=v)) ↔
    ((∀ u, A u → B u → r u=u) ∧ (∀ u, A u → ¬ B u → ¬ B (r u))) := by
  constructor
  · intro h
    constructor
    · intro u ha hb; exact (h u u ha hb).mpr rfl
    · intro u ha hn hb
      have eq := (h u (r u) ha hb).mp rfl
      exact hn (eq.symm ▸ hb)
  · rintro ⟨fixed,noextra⟩ u v ha hb
    constructor
    · intro eq
      by_cases bu : B u
      · exact (fixed u ha bu).symm.trans eq
      · exact False.elim (noextra u ha bu (eq.symm ▸ hb))
    · intro eq; subst v; exact fixed u ha hb

#print axioms injective
#print axioms pairCriterion
#print axioms wholeSetCriterion
#print axioms imagePath
#print axioms matchingSplit
end FibreSymmetry204
