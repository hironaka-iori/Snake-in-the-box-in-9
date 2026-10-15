import CubeLocal

namespace RadiusThreeForest
open Snake9
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def components : Array (Array Nat) := #[
  #[134, 132, 140, 136, 138, 10, 2, 0, 1, 5, 261, 260, 268, 264, 265],
  #[22, 20, 28, 24, 25],
  #[38, 36, 44, 40, 41],
  #[49, 48, 50],
  #[70, 68, 76, 72, 73],
  #[81, 80, 82],
  #[97, 96, 98],
  #[145, 144, 146],
  #[161, 160, 162],
  #[193, 192, 194],
  #[273, 272, 274],
  #[289, 288, 290],
  #[321, 320, 322],
  #[385, 384, 386]
]

def edgeCount (c : Fin 14) : Nat := (components[c.val]!).size-1
def vertex (c : Fin 14) (i : Fin (edgeCount c+1)) : Vertex :=
  ⟨(components[c.val]!)[i.val]! % 512,Nat.mod_lt _ (by decide)⟩

theorem component_distinct : ∀ c : Fin 14, ∀ i j : Fin (edgeCount c+1),
    vertex c i=vertex c j → i=j := by decide

theorem component_induced : ∀ c : Fin 14, ∀ i j : Fin (edgeCount c+1), i.val<j.val →
    (Adj (vertex c i) (vertex c j) ↔ i.val+1=j.val) := by decide

def path (c : Fin 14) : Snake (edgeCount c) :=
  ⟨vertex c,component_distinct c,component_induced c⟩

theorem components_separated : ∀ c d : Fin 14, c≠d →
    ∀ i : Fin (edgeCount c+1), ∀ j : Fin (edgeCount d+1),
    vertex c i≠vertex d j ∧ ¬ Adj (vertex c i) (vertex d j) := by decide

def vertices : List Vertex := (List.finRange 14).flatMap
  (fun c => (List.finRange (edgeCount c+1)).map (vertex c))

def weight (v : Vertex) : Nat := ((List.range 9).filter (fun k => v.val.testBit k)).length

def degree (v : Vertex) : Nat := (vertices.filter (fun w => decide (Adj v w))).length

theorem root_selected : (0 : Vertex) ∈ vertices := by decide

theorem inside_radius_three : ∀ c : Fin 14, ∀ i : Fin (edgeCount c+1), weight (vertex c i)≤3 := by decide

theorem radius_two_vertices_internal : ∀ c : Fin 14, ∀ i : Fin (edgeCount c+1),
    weight (vertex c i)≤2 → degree (vertex c i)=2 := by decide

def singletonPairsAtZero : List (Nat × Nat) :=
  ((List.range 9).flatMap (fun a => (List.range 9).map (fun b => (a,b)))).filter
    (fun ab => decide (ab.1<ab.2) && vertices.all (fun v =>
      v.val != 2^ab.1 && v.val != 2^ab.2 && v.val != Nat.xor (2^ab.1) (2^ab.2)))

theorem one_singleton_square : singletonPairsAtZero=[(2,3)] := by decide

#print axioms path
#print axioms components_separated
#print axioms inside_radius_three
#print axioms radius_two_vertices_internal
#print axioms one_singleton_square
end RadiusThreeForest
