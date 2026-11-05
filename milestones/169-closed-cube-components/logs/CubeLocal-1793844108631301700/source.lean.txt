import PathStructure

namespace Snake9
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev Coord := Fin 9

def vxor (u v : Vertex) : Vertex :=
  ⟨u.val ^^^ v.val, Nat.xor_lt_two_pow (n:=9) u.isLt v.isLt⟩

def unit (a : Coord) : Vertex :=
  ⟨2^a.val, (by
    have h : ∀ a : Coord, 2^a.val < 512 := by decide
    exact h a)⟩

def pair (a b : Coord) : Vertex := vxor (unit a) (unit b)
def triple (a b c : Coord) : Vertex := vxor (pair a b) (unit c)

theorem vxor_self (v : Vertex) : vxor v v = 0 := by
  apply Fin.ext
  exact Nat.xor_self v.val

theorem vxor_cancel (v u : Vertex) : vxor v (vxor v u) = u := by
  apply Fin.ext
  change v.val ^^^ (v.val ^^^ u.val) = u.val
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem vxor_injective (v : Vertex) {a b : Vertex} (h : vxor v a=vxor v b) : a=b := by
  have := congrArg (vxor v) h
  simpa only [vxor_cancel] using this

theorem adj_vxor (t u v : Vertex) : Adj (vxor t u) (vxor t v) ↔ Adj u v := by
  simp only [adj_iff_coordinate_flip]
  constructor
  · rintro ⟨k,hk,he⟩
    refine ⟨k,hk,?_⟩
    have hh := congrArg (fun z => t.val ^^^ z) he
    change t.val ^^^ (t.val ^^^ v.val) = t.val ^^^ ((t.val ^^^ u.val) ^^^ 2^k) at hh
    simp only [Nat.xor_assoc, ← Nat.xor_assoc t.val t.val, Nat.xor_self, Nat.zero_xor] at hh
    exact hh
  · rintro ⟨k,hk,he⟩
    refine ⟨k,hk,?_⟩
    change t.val ^^^ v.val = (t.val ^^^ u.val) ^^^ 2^k
    rw [he]
    exact (Nat.xor_assoc _ _ _).symm

def translate {m : Nat} (p : Snake m) (t : Vertex) : Snake m where
  vertex i := vxor t (p.vertex i)
  distinct i j h := p.distinct i j (vxor_injective t h)
  induced i j hij := by rw [adj_vxor]; exact p.induced i j hij

theorem adj_zero_iff (v : Vertex) : Adj 0 v ↔ ∃ a : Coord, v=unit a := by
  constructor
  · intro h
    obtain ⟨k,hk,he⟩ := (adj_iff_coordinate_flip 0 v).mp h
    refine ⟨⟨k,hk⟩,Fin.ext ?_⟩
    change v.val = 0 ^^^ 2^k at he
    change v.val = 2^k
    simpa only [Nat.zero_xor] using he
  · rintro ⟨a,rfl⟩
    apply (adj_iff_coordinate_flip 0 (unit a)).mpr
    exact ⟨a.val,a.isLt,(Nat.zero_xor _).symm⟩

theorem neighbor_unit (a : Coord) {v : Vertex} (h : Adj (unit a) v) :
    ∃ b : Coord, v=pair a b := by
  obtain ⟨k,hk,he⟩ := (adj_iff_coordinate_flip _ _).mp h
  exact ⟨⟨k,hk⟩,Fin.ext he⟩

theorem neighbor_pair (a b : Coord) {v : Vertex} (h : Adj (pair a b) v) :
    ∃ c : Coord, v=triple a b c := by
  obtain ⟨k,hk,he⟩ := (adj_iff_coordinate_flip _ _).mp h
  exact ⟨⟨k,hk⟩,Fin.ext he⟩

theorem unit_injective : ∀ a b : Coord, unit a=unit b → a=b := by decide

theorem pair_comm (a b : Coord) : pair a b = pair b a := by
  apply Fin.ext
  exact Nat.xor_comm _ _

theorem pair_injective_right (a b c : Coord) (h : pair a b = pair a c) : b=c := by
  exact unit_injective b c (vxor_injective (unit a) h)

theorem pair_triple_adj (a b c : Coord) : Adj (pair a b) (triple a b c) := by
  apply (adj_iff_coordinate_flip _ _).mpr
  exact ⟨c.val, c.isLt, rfl⟩

theorem triple_swap (a b c : Coord) : triple a b c = triple a c b := by
  apply Fin.ext
  change ((unit a).val ^^^ (unit b).val) ^^^ (unit c).val =
    ((unit a).val ^^^ (unit c).val) ^^^ (unit b).val
  rw [Nat.xor_assoc, Nat.xor_comm (unit b).val (unit c).val, ← Nat.xor_assoc]

theorem triple_cancel_left (a b : Coord) : triple a b a = unit b := by
  apply Fin.ext
  change ((unit a).val ^^^ (unit b).val) ^^^ (unit a).val = (unit b).val
  rw [Nat.xor_comm (unit a).val (unit b).val, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem triple_cancel_right (a b : Coord) : triple a b b = unit a := by
  apply Fin.ext
  change ((unit a).val ^^^ (unit b).val) ^^^ (unit b).val = (unit a).val
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem triple_adj_sides (i j k : Coord) :
    Adj (triple i j k) (pair i j) ∧ Adj (triple i j k) (pair i k) ∧
      Adj (triple i j k) (pair j k) := by
  refine ⟨adj_symmetric (pair_triple_adj i j k), ?_, ?_⟩
  · rw [triple_swap i j k]
    exact adj_symmetric (pair_triple_adj i k j)
  · have he : triple i j k = triple j i k := by simp only [triple, pair_comm i j]
    rw [he, triple_swap j i k]
    exact adj_symmetric (pair_triple_adj j k i)

theorem three_pairs_distinct (i j k : Coord) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    pair i j ≠ pair i k ∧ pair i j ≠ pair j k ∧ pair i k ≠ pair j k := by
  refine ⟨fun h => hjk (pair_injective_right i j k h), ?_, ?_⟩
  · intro h
    rw [pair_comm i j] at h
    exact hik (pair_injective_right j i k h)
  · intro h
    rw [pair_comm i k, pair_comm j k] at h
    exact hij (pair_injective_right k i j h)

#print axioms translate
#print axioms triple_adj_sides
#print axioms three_pairs_distinct
end Snake9
