import SquareCounterexample

namespace EndpointFourWitness
open Snake9 SquareCounterexample
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A local sharpness example found by the endpoint-count search.
    This is not a record-length Q9 construction. -/
def values : Array Nat := #[0, 1, 129, 193, 192, 208, 144, 148, 20, 84, 68, 69, 77, 13, 12, 140, 136, 392, 384, 388, 260, 261, 263, 279, 23, 19, 18, 50, 48, 112, 96, 98, 66, 67, 75, 107, 105, 41, 40, 42, 10, 266, 258, 290, 288, 289, 353, 321, 320, 328, 72, 88, 24, 280, 272, 273, 401, 433, 437, 309, 317, 285, 413, 477, 221, 253, 255, 247, 243, 115, 371, 307, 315, 299, 427, 395, 139, 155, 219, 475, 347, 351, 383, 367, 365, 493, 492, 428, 430, 422, 438, 310, 374, 342, 326, 454, 455, 199, 207, 206, 238, 234, 250, 506, 510, 478, 414, 158, 190, 62, 63, 47, 39, 37, 36, 164, 160, 162, 130, 134, 6]

def vertex (i : Fin 121) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem distinct : ∀ i j : Fin 121, vertex i = vertex j → i = j := by decide

theorem induced : ∀ i j : Fin 121, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by decide

def path : Snake 120 := ⟨vertex,distinct,induced⟩

theorem initial_vertex : (path.vertex 0).val = 0 := by decide

theorem endpoint_singleton_squares : singletonPairs path 0 = [(1,5), (2,7), (3,8), (4,6)] := by decide

theorem endpoint_singleton_count : (singletonPairs path 0).length = 4 := by
  rw [endpoint_singleton_squares]
  decide

#print axioms distinct
#print axioms induced
#print axioms endpoint_singleton_squares
#print axioms endpoint_singleton_count
end EndpointFourWitness
