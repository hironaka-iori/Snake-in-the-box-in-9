import OrdinaryOuterBase

namespace Snake9
open Finset Classical
noncomputable section

def OrdinaryPartnerClear (F : Finset (Finset Coord)) (R A B : Finset Coord)
    (k s : Coord) : Prop :=
  ∀r∈R,(({k,r}:Finset Coord)=A ∨ ({k,r}:Finset Coord)=B) → ({s,r}:Finset Coord)∉F

def OrdinaryGoodRow (F : Finset (Finset Coord)) (R A B : Finset Coord)
    (c d k : Coord) : Prop :=
  PairIsolated F k ∧
    ((OrdinaryPartnerClear F R A B k c ∧ OrdinaryPartnerClear F R A B k d) ∨
     (({c,d}:Finset Coord)∉F ∧
       (OrdinaryPartnerClear F R A B k c ∨ OrdinaryPartnerClear F R A B k d)))

def ordinaryGoodIndices (F : Finset (Finset Coord)) (R A B : Finset Coord)
    (c d : Coord) : Finset Coord := R.filter (OrdinaryGoodRow F R A B c d)

def ordinaryEndpointDemand (F : Finset (Finset Coord)) (R A B : Finset Coord)
    (c d : Coord) : Nat :=
  (ordinaryGoodIndices F R A B c d).card+
  (F.filter (fun s => s⊆R ∧ Disjoint s A)).card+
  (F.filter (fun s => s⊆R ∧ Disjoint s B)).card+
  (if OrdinaryHoleGood F R c d A B then 1 else 0)+
  (if OrdinaryHoleGood F R c d B A then 1 else 0)

end
end Snake9
