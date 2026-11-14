import Std
namespace DiagonalExtension205
abbrev Square := Bool × Bool
def parity (u : Square) : Bool := Bool.xor u.1 u.2
def opposite (u : Square) : Square := (!u.1,!u.2)
def displacement (u v : Square) : Bool := Bool.xor u.1 v.1
def act (f : Bool → Bool) (u : Square) : Square := if f (parity u) then opposite u else u

theorem sameDisplacement (u v u' v' : Square)
    (same : parity u=parity v) (pu : parity u'=parity u) (pv : parity v'=parity v)
    (equal : u=v ↔ u'=v') : displacement u u'=displacement v v' := by
  rcases u with ⟨a,b⟩; rcases v with ⟨c,d⟩; rcases u' with ⟨e,f⟩; rcases v' with ⟨g,h⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> cases h <;>
    simp_all [parity,displacement]

theorem reconstruction (u v : Square) (same : parity v=parity u) :
    v=if displacement u v then opposite u else u := by
  rcases u with ⟨a,b⟩; rcases v with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [parity,displacement,opposite]

theorem selectedExtension (S : Square → Prop) (g : Square → Square)
    (inj : ∀ u v, S u → S v → g u=g v → u=v)
    (preserve : ∀ u, S u → parity (g u)=parity u) :
    ∃ f : Bool → Bool, ∀ u, S u → g u=act f u := by
  classical
  let f : Bool → Bool := fun e => decide (∃ u, S u ∧ parity u=e ∧ displacement u (g u)=true)
  have phase : ∀ u, S u → f (parity u)=displacement u (g u) := by
    intro u hu
    cases hd : displacement u (g u)
    · have no : ¬(∃ v, S v ∧ parity v=parity u ∧ displacement v (g v)=true) := by
        rintro ⟨v,hv,hp,hvdis⟩
        have eq : u=v ↔ g u=g v := ⟨congrArg g,inj u v hu hv⟩
        have same := sameDisplacement u v (g u) (g v) hp.symm (preserve u hu) (preserve v hv) eq
        simp [hd,hvdis] at same
      simp only [f,no,decide_false]
    · have yes : ∃ v, S v ∧ parity v=parity u ∧ displacement v (g v)=true := ⟨u,hu,rfl,hd⟩
      simp only [f,yes,decide_true]
  refine ⟨f,?_⟩
  intro u hu
  simp only [act,phase u hu]
  exact reconstruction u (g u) (preserve u hu)

theorem oppositeParity (u : Square) : parity (opposite u)=parity u := by
  rcases u with ⟨a,b⟩; cases a <;> cases b <;> rfl
theorem actParity (f : Bool → Bool) (u : Square) : parity (act f u)=parity u := by
  unfold act; split <;> simp_all [oppositeParity]
theorem actInvolution (f : Bool → Bool) (u : Square) : act f (act f u)=u := by
  rw [act,actParity]
  cases h : f (parity u) <;> simp [act,h,opposite]

#print axioms sameDisplacement
#print axioms reconstruction
#print axioms selectedExtension
#print axioms oppositeParity
#print axioms actParity
#print axioms actInvolution
end DiagonalExtension205
