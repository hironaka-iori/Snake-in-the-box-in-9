import Std
namespace Replacement191

def colourSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => colourSum f n + f n

theorem pairedCount (k : Nat) (f : Nat → Nat)
    (hpairs : ∀ i, i < k → f (2*i)+f (2*i+1)=1) :
    colourSum f (2*k)=k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := ih (by intro i hi; exact hpairs i (by omega))
    have hp := hpairs k (by omega)
    have hn : 2*(k+1)=(2*k+1)+1 := by omega
    rw [hn]
    simp only [colourSum]
    omega

theorem alternatingColourCount (k : Nat) (f : Nat → Nat)
    (halt : ∀ i, i+1 < 2*k → f i+f (i+1)=1) :
    colourSum f (2*k)=k := by
  apply pairedCount
  intro i hi
  exact halt (2*i) (by omega)

theorem replacement95to97 (f g : Nat → Nat)
    (hf : ∀ i, i+1 < 96 → f i+f (i+1)=1)
    (hg : ∀ i, i+1 < 98 → g i+g (i+1)=1) :
    colourSum g 98 = colourSum f 96 + 1 := by
  have h1 := alternatingColourCount 48 f hf
  have h2 := alternatingColourCount 49 g hg
  change colourSum f 96 = 48 at h1
  change colourSum g 98 = 49 at h2
  omega

theorem singletonRequirement (added components singletons : Nat)
    (hcomponents : singletons ≤ components)
    (hsize : singletons+2*(components-singletons) ≤ added) :
    2*components ≤ added+singletons := by omega

#print axioms pairedCount
#print axioms alternatingColourCount
#print axioms replacement95to97
#print axioms singletonRequirement
end Replacement191
