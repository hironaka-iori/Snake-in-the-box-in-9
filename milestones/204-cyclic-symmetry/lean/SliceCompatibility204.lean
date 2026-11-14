import FibreSymmetry204
namespace SliceCompatibility204
open FibreSymmetry204

theorem relativeMatching {W : Type} (g gi h : W → W)
    (left : ∀ u, gi (g u)=u) (right : ∀ u, g (gi u)=u) (u v : W) :
    h v=g u ↔ gi (h v)=u := by
  constructor
  · intro eq; rw [eq,left]
  · intro eq; have e := congrArg g eq; simpa only [right] using e

theorem gluingCriterion {W : Type} (A B : W → Prop) (g gi h : W → W)
    (left : ∀ u, gi (g u)=u) (right : ∀ u, g (gi u)=u) :
    (∀ v u, B v → A u → (h v=g u ↔ v=u)) ↔
    ((∀ v, B v → A v → gi (h v)=v) ∧
     (∀ v, B v → ¬ A v → ¬ A (gi (h v)))) := by
  have matchEq : (∀ v u, B v → A u → (h v=g u ↔ v=u)) ↔
      (∀ v u, B v → A u → (gi (h v)=u ↔ v=u)) := by
    simp only [relativeMatching g gi h left right]
  exact matchEq.trans (matchingSplit B A (fun v => gi (h v)))

def centred {I : Type} (pi : I → I) (c x : I → Bool) (i : I) : Bool :=
  Bool.xor (c i) (Bool.xor (x (pi i)) (c (pi i)))
def normal {I : Type} (c x : I → Bool) (i : I) : Bool := Bool.xor (x i) (c i)

theorem bitFixed {I : Type} (pi : I → I) (c x : I → Bool) (i : I) :
    centred pi c x i=x i ↔ normal c x (pi i)=normal c x i := by
  cases a : c i <;> cases b : x i <;> cases d : c (pi i) <;> cases e : x (pi i) <;>
    simp [centred,normal,a,b,d,e]

theorem columnCriterion {I : Type} (pi : I → I) (c : I → Bool) (S : (I → Bool) → Prop) :
    (∀ x, S x → centred pi c x=x) ↔
    (∀ i x, S x → normal c x (pi i)=normal c x i) := by
  constructor
  · intro fixed i x hx
    exact (bitFixed pi c x i).mp (congrFun (fixed x hx) i)
  · intro cols x hx; funext i
    exact (bitFixed pi c x i).mpr (cols i x hx)

theorem distinctColumnsRigid {I : Type} (pi : I → I) (c : I → Bool) (S : (I → Bool) → Prop)
    (distinct : ∀ i j, (∀ x, S x → normal c x i=normal c x j) → i=j)
    (fixed : ∀ x, S x → centred pi c x=x) :
    (∀ i, pi i=i) ∧ (∀ x, centred pi c x=x) := by
  have same : ∀ i, pi i=i := fun i => distinct (pi i) i ((columnCriterion pi c S).mp fixed i)
  refine ⟨same,?_⟩
  intro x; funext i
  simp only [centred,same]
  cases c i <;> cases x i <;> rfl

theorem representativeTransfer {W : Type} (A B : W → Prop) (g g' h : W → W)
    (same : ∀ u, A u → g' u=g u)
    (compatible : ∀ v u, B v → A u → (h v=g u ↔ v=u)) :
    ∀ v u, B v → A u → (h v=g' u ↔ v=u) := by
  intro v u hv hu; rw [same u hu]; exact compatible v u hv hu

theorem relativeReconstruction {W : Type} (g gi h : W → W)
    (right : ∀ u, g (gi u)=u) : ∀ u, g (gi (h u))=h u := fun u => right (h u)

theorem commonLeft {W : Type} (g : W → W) (inj : ∀ u v, g u=g v → u=v)
    (u v : W) : g u=g v ↔ u=v := ⟨inj u v,congrArg g⟩

#print axioms relativeMatching
#print axioms gluingCriterion
#print axioms bitFixed
#print axioms columnCriterion
#print axioms distinctColumnsRigid
#print axioms representativeTransfer
#print axioms relativeReconstruction
#print axioms commonLeft
end SliceCompatibility204
