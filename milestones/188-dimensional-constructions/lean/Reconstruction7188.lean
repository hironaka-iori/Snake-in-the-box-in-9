import TwoCrossings188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Reconstruction7
open LayerJoining
def Adj (u v : Fin 64) : Prop := (List.range 6).any (fun k => v.val == Nat.xor u.val (2^k)) = true
instance (u v : Fin 64) : Decidable (Adj u v) := inferInstanceAs (Decidable (_ = true))
def pValues : Array Nat := #[0, 1, 3, 7, 6, 14, 12, 13, 29, 25, 27, 26, 18, 50, 51, 49, 53, 37, 36]
def pVertex (i : Fin 19) : Fin 64 :=
  ⟨pValues[i.val]! % 64,Nat.mod_lt _ (by decide)⟩
theorem p_distinct : ∀ i j, pVertex i = pVertex j → i=j := by decide +kernel
theorem p_induced : ∀ i j, i.val < j.val → (Adj (pVertex i) (pVertex j) ↔ i.val+1=j.val) := by decide +kernel
def p : LayerJoining.InducedPath (Fin 64) Adj 18 := ⟨pVertex,p_distinct,p_induced⟩
#print axioms p_distinct
#print axioms p_induced
def qValues : Array Nat := #[36, 4, 5, 21, 17, 16, 24, 8, 9, 11, 15, 31, 30, 22, 54, 55, 39, 35, 34, 42, 58, 59, 57, 61, 60]
def qVertex (i : Fin 25) : Fin 64 :=
  ⟨qValues[i.val]! % 64,Nat.mod_lt _ (by decide)⟩
theorem q_distinct : ∀ i j, qVertex i = qVertex j → i=j := by decide +kernel
theorem q_induced : ∀ i j, i.val < j.val → (Adj (qVertex i) (qVertex j) ↔ i.val+1=j.val) := by decide +kernel
def q : LayerJoining.InducedPath (Fin 64) Adj 24 := ⟨qVertex,q_distinct,q_induced⟩
#print axioms q_distinct
#print axioms q_induced
def rValues : Array Nat := #[60, 56, 40, 41, 43, 47, 63]
def rVertex (i : Fin 7) : Fin 64 :=
  ⟨rValues[i.val]! % 64,Nat.mod_lt _ (by decide)⟩
theorem r_distinct : ∀ i j, rVertex i = rVertex j → i=j := by decide +kernel
theorem r_induced : ∀ i j, i.val < j.val → (Adj (rVertex i) (rVertex j) ↔ i.val+1=j.val) := by decide +kernel
def r : LayerJoining.InducedPath (Fin 64) Adj 6 := ⟨rVertex,r_distinct,r_induced⟩
#print axioms r_distinct
#print axioms r_induced
theorem pq : Compatible p q := by
  unfold Compatible
  decide +kernel
theorem qr : Compatible q r := by
  unfold Compatible
  decide +kernel
theorem pr : ∀ i j, p.vertex i ≠ r.vertex j ∧ ¬ Adj (p.vertex i) (r.vertex j) := by decide +kernel
def reconstructed : InducedPath (Fin 64 × Bool) (LayerAdj Adj) 50 := twoCrossings p q r pq qr pr
#print axioms pq
#print axioms qr
#print axioms pr
#print axioms reconstructed
end Dimensional188.Reconstruction7
