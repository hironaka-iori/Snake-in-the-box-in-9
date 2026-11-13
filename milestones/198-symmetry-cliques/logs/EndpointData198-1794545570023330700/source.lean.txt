import CliqueFacts198
namespace EndpointData198

def rawNeighbour (v k : Nat) : Nat :=
 if k<7 then Nat.xor v (2^k) else CliqueFacts198.matching v
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def neighbour (v : Fin 128) (k : Fin 8) : Fin 128 :=
 ⟨rawNeighbour v.val k.val % 128, Nat.mod_lt _ (by decide)⟩
def Adj (v w : Fin 128) : Prop := ∃ k : Fin 8, neighbour v k=w

def exchange (v : Nat) : Nat :=
 let a := Nat.xor v (if CliqueFacts198.bit v 1 == CliqueFacts198.bit v 3 then 0 else 10)
 Nat.xor a (if CliqueFacts198.bit a 4 == CliqueFacts198.bit a 6 then 0 else 80)
def masks : Array Nat := #[1,4,32,18,72]
def rawGenerator (k v : Nat) : Nat := if k=5 then exchange v else Nat.xor v masks[k]!

def generator (k : Fin 6) (v : Fin 128) : Fin 128 :=
 ⟨rawGenerator k.val v.val % 128, Nat.mod_lt _ (by decide)⟩
def directionTable : Array Nat := #[0,3,2,1,6,5,4,7]
def rawDirection (k d : Nat) : Nat := if k=5 then directionTable[d]! else d

def direction (k : Fin 6) (d : Fin 8) : Fin 8 :=
 ⟨rawDirection k.val d.val % 8, Nat.mod_lt _ (by decide)⟩

def words : Array (List (Fin 6)) := #[[],
 [⟨0,by decide⟩],
 [],
 [⟨0,by decide⟩],
 [⟨1,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩],
 [⟨1,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩],
 [⟨5,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩],
 [],
 [⟨0,by decide⟩],
 [⟨5,by decide⟩, ⟨1,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨1,by decide⟩],
 [⟨1,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩],
 [⟨3,by decide⟩],
 [⟨0,by decide⟩, ⟨3,by decide⟩],
 [⟨3,by decide⟩],
 [⟨0,by decide⟩, ⟨3,by decide⟩],
 [⟨1,by decide⟩, ⟨3,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨3,by decide⟩],
 [⟨1,by decide⟩, ⟨3,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨3,by decide⟩],
 [⟨3,by decide⟩],
 [⟨0,by decide⟩, ⟨3,by decide⟩],
 [⟨5,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨4,by decide⟩],
 [⟨1,by decide⟩, ⟨3,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨3,by decide⟩],
 [⟨5,by decide⟩, ⟨1,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨1,by decide⟩, ⟨4,by decide⟩],
 [⟨2,by decide⟩],
 [⟨0,by decide⟩, ⟨2,by decide⟩],
 [⟨2,by decide⟩],
 [⟨0,by decide⟩, ⟨2,by decide⟩],
 [⟨1,by decide⟩, ⟨2,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩],
 [⟨1,by decide⟩, ⟨2,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩],
 [⟨5,by decide⟩, ⟨2,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨2,by decide⟩],
 [⟨2,by decide⟩],
 [⟨0,by decide⟩, ⟨2,by decide⟩],
 [⟨5,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩],
 [⟨1,by decide⟩, ⟨2,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩],
 [⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨0,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨0,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨0,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨5,by decide⟩, ⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨5,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨3,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨3,by decide⟩],
 [⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨1,by decide⟩, ⟨3,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨1,by decide⟩, ⟨3,by decide⟩],
 [⟨1,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨4,by decide⟩],
 [⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨4,by decide⟩],
 [⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨4,by decide⟩],
 [⟨1,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨4,by decide⟩],
 [⟨1,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨4,by decide⟩],
 [⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨1,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨1,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨1,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨1,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨1,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩],
 [⟨1,by decide⟩, ⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨1,by decide⟩, ⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨1,by decide⟩, ⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨4,by decide⟩],
 [⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨5,by decide⟩, ⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩],
 [⟨0,by decide⟩, ⟨1,by decide⟩, ⟨2,by decide⟩, ⟨3,by decide⟩, ⟨4,by decide⟩]]
def word (v : Fin 128) : List (Fin 6) := words[v.val]!
def evaluate : List (Fin 6) → Fin 128 → Fin 128
 | [],v => v
 | k::ks,v => evaluate ks (generator k v)

theorem cover {P : Fin 128 → Prop}
 (h : ∀ b : Fin 8, ∀ i : Fin 16, P ⟨16*b.val+i.val,by omega⟩)
 (v : Fin 128) : P v := by
 have he : 16*(v.val/16)+v.val%16=v.val := by omega
 have hv := h ⟨v.val/16,by omega⟩ ⟨v.val%16,by omega⟩
 simpa only [Fin.val_mk,he] using hv

#print axioms cover
end EndpointData198
