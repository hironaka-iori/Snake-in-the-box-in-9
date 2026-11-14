import BlockSymmetry203
namespace BlockRigidity203
open BlockSymmetry203 LayerJoining

theorem affectedLeft {W : Type} (h : W → W) (inv : ∀ u, h (h u)=u) (u v : W) :
    affected h (h u) v ↔ affected h u v := by
  simp only [affected,inv]
  simp [ne_comm,or_comm]

theorem affectedRight {W : Type} (h : W → W) (inv : ∀ u, h (h u)=u) (u v : W) :
    affected h u (h v) ↔ affected h u v := by
  have hi : h u=h v ↔ u=v := ⟨hInjective h inv u v,congrArg h⟩
  simp only [affected,crossEquality h inv,hi,inv]
  simp [or_comm]

theorem orbitInvariant {W : Type} (h : W → W) (inv : ∀ u, h (h u)=u)
    (c d : Bool) (u v : W) :
    affected h (twist h c u) (twist h d v) ↔ affected h u v := by
  cases c <;> cases d <;> simp [twist,affectedLeft h inv,affectedRight h inv]

theorem compose {V W : Type} (h : W → W) (inv : ∀ u, h (h u)=u)
    (f g : V → Bool) (x : V × W) :
    change h f (change h g x)=change h (fun z => Bool.xor (f z) (g z)) x := by
  rcases x with ⟨z,u⟩
  cases a : f z <;> cases b : g z <;> simp [change,twist,a,b,inv]

theorem selectorConstant {V W : Type} {R : V → V → Prop} {T : W → W → Prop} {m : Nat}
    (p : InducedPath (V × W) (Adj R T) m) (h : W → W) (f : V → Bool)
    (moved : ∀ i, h (p.vertex i).2 ≠ (p.vertex i).2)
    (compatible : ∀ i j, R (p.vertex i).1 (p.vertex j).1 →
      affected h (p.vertex i).2 (p.vertex j).2 → f (p.vertex i).1=f (p.vertex j).1) :
    ∀ i, f (p.vertex i).1=f (p.vertex ⟨0,by omega⟩).1 := by
  have walk : ∀ n (hn : n<m+1), f (p.vertex ⟨n,hn⟩).1=f (p.vertex ⟨0,by omega⟩).1 := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      have hn0 : n<m+1 := by omega
      have edge := (p.induced ⟨n,hn0⟩ ⟨n+1,hn⟩ (by simp)).mpr (by rfl)
      have step : f (p.vertex ⟨n,hn0⟩).1=f (p.vertex ⟨n+1,hn⟩).1 := by
        rcases edge with same | cross
        · rw [same.1]
        · exact compatible _ _ cross.1 ⟨moved _,Or.inl cross.2⟩
      exact step.symm.trans (ih hn0)
  intro i; exact walk i.val i.isLt

theorem noFixedVertexRigid {V W : Type} {R : V → V → Prop} {T : W → W → Prop} {m : Nat}
    (p : InducedPath (V × W) (Adj R T) m) (h : W → W) (f : V → Bool)
    (moved : ∀ i, h (p.vertex i).2 ≠ (p.vertex i).2)
    (compatible : ∀ i j, R (p.vertex i).1 (p.vertex j).1 →
      affected h (p.vertex i).2 (p.vertex j).2 → f (p.vertex i).1=f (p.vertex j).1) :
    ∀ i, change h f (p.vertex i)=change h (fun _ => f (p.vertex ⟨0,by omega⟩).1) (p.vertex i) := by
  intro i
  have hh := selectorConstant p h f moved compatible i
  simp only [change,hh]

#print axioms affectedLeft
#print axioms affectedRight
#print axioms orbitInvariant
#print axioms compose
#print axioms selectorConstant
#print axioms noFixedVertexRigid
end BlockRigidity203
