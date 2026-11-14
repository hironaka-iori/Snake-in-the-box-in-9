import Std
set_option Elab.async false
namespace CubeThree205
abbrev Word := Bool × Bool × Bool
def parity (u : Word) : Bool := Bool.xor u.1 (Bool.xor u.2.1 u.2.2)
def opposite (u : Word) : Word := (!u.1,!u.2.1,!u.2.2)
def colour (u : Word) : Word := if parity u then opposite u else u
def adjacent (u v : Word) : Prop :=
  (u.1≠v.1 ∧ u.2.1=v.2.1 ∧ u.2.2=v.2.2) ∨
  (u.1=v.1 ∧ u.2.1≠v.2.1 ∧ u.2.2=v.2.2) ∨
  (u.1=v.1 ∧ u.2.1=v.2.1 ∧ u.2.2≠v.2.2)
theorem colourEven (u : Word) : parity (colour u)=false := by
  rcases u with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> rfl
theorem colourOpposite (u : Word) : colour (opposite u)=colour u := by
  rcases u with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> rfl
theorem sameParityColour (u v : Word) (h : parity u=parity v) :
    colour u=colour v ↔ u=v := by
  rcases u with ⟨a,b,c⟩; rcases v with ⟨d,e,f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    simp_all [parity,colour,opposite]
theorem oppositeParityAdjacency (u v : Word) (h : parity u≠parity v) :
    adjacent u v ↔ colour u≠colour v := by
  rcases u with ⟨a,b,c⟩; rcases v with ⟨d,e,f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    simp_all [parity,colour,opposite,adjacent]
theorem selectedColourCorrespondence (S : Word → Prop) (g : Word → Word)
    (inj : ∀ u v, S u → S v → g u=g v → u=v)
    (preserve : ∀ u, S u → parity (g u)=parity u)
    (pairs : ∀ u v, S u → S v → (adjacent u v ↔ adjacent (g u) (g v))) :
    ∀ u v, S u → S v → (colour u=colour v ↔ colour (g u)=colour (g v)) := by
  intro u v hu hv
  by_cases same : parity u=parity v
  · have target : parity (g u)=parity (g v) := (preserve u hu).trans (same.trans (preserve v hv).symm)
    rw [sameParityColour u v same,sameParityColour (g u) (g v) target]
    exact ⟨congrArg g,inj u v hu hv⟩
  · have target : parity (g u)≠parity (g v) := by
      rw [preserve u hu,preserve v hv]
      exact same
    have different : colour u≠colour v ↔ colour (g u)≠colour (g v) :=
      (oppositeParityAdjacency u v same).symm.trans ((pairs u v hu hv).trans (oppositeParityAdjacency (g u) (g v) target))
    constructor
    · intro equal
      exact Classical.byContradiction (fun h => (different.mpr h) equal)
    · intro equal
      exact Classical.byContradiction (fun h => (different.mp h) equal)
#print axioms colourEven
#print axioms colourOpposite
#print axioms sameParityColour
#print axioms oppositeParityAdjacency
#print axioms selectedColourCorrespondence
def distance4 (a b : Nat) : Nat :=
  (List.range 4).foldl (fun total i => total + if (Nat.xor a b).testBit i then 1 else 0) 0
theorem fourCoordinateData :
    distance4 0 3=2 ∧ distance4 0 15=4 ∧
    distance4 0 0 % 2=0 ∧ distance4 0 3 % 2=0 ∧ distance4 0 15 % 2=0 := by
  decide +kernel
#print axioms fourCoordinateData
def smallSource : Array Nat := #[0,1,3,7,6]
def smallTarget : Array Nat := #[0,1,3,7,15]
theorem smallPaths :
    (∀ i : Fin 5, smallSource[i.val]! < 16 ∧ smallTarget[i.val]! < 16 ∧
      distance4 0 smallSource[i.val]! % 2 = distance4 0 smallTarget[i.val]! % 2) ∧
    (∀ i j : Fin 5, i≠j →
      smallSource[i.val]!≠smallSource[j.val]! ∧ smallTarget[i.val]!≠smallTarget[j.val]! ∧
      (distance4 smallSource[i.val]! smallSource[j.val]! = 1 ↔ i.val+1=j.val ∨ j.val+1=i.val) ∧
      (distance4 smallTarget[i.val]! smallTarget[j.val]! = 1 ↔ i.val+1=j.val ∨ j.val+1=i.val)) ∧
    distance4 smallSource[0]! smallSource[4]! = 2 ∧
    distance4 smallTarget[0]! smallTarget[4]! = 4 := by
  decide +kernel
#print axioms smallPaths
end CubeThree205
