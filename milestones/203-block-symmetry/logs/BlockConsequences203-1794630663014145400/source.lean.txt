import BlockSymmetry203
namespace BlockConsequences203
open BlockSymmetry203

theorem orbitMatching {W : Type} (h : W → W) (inv : ∀ u, h (h u)=u)
    (u : W) (moved : h u ≠ u) (c d r : Bool) :
    twist h c u=twist h d (twist h r u) ↔ Bool.xor c d=r := by
  cases c <;> cases d <;> cases r <;> simp [twist,inv,moved,Ne.symm moved]

def affine {I : Type} (pi : I → I) (t x : I → Bool) (i : I) : Bool :=
  Bool.xor (x (pi i)) (t i)

theorem fixedConjugacy {I : Type} (pi : I → I) (t c x : I → Bool)
    (fixed : affine pi t c=c) (i : I) :
    affine pi t x i=Bool.xor (c i) (Bool.xor (x (pi i)) (c (pi i))) := by
  have hf := congrFun fixed i
  cases a : x (pi i) <;> cases b : c i <;> cases d : c (pi i) <;> cases e : t i <;>
    simp_all [affine]

#print axioms orbitMatching
#print axioms fixedConjugacy
end BlockConsequences203
