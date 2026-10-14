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
 theorem unit_nonzero : ∀ a : Coord, unit a ≠ 0 := by decide
 theorem pair_self : ∀ a : Coord, pair a a=0 := by decide
 theorem pair_comm : ∀ a b : Coord, pair a b=pair b a := by decide
 theorem pair_nonzero : ∀ a b : Coord, a≠b → pair a b≠0 := by decide
 theorem pair_injective_right : ∀ a b c : Coord, pair a b=pair a c → b=c := by decide
 theorem unit_pair_adj : ∀ a b : Coord, Adj (unit a) (pair a b) := by decide
 theorem pair_triple_adj : ∀ a b c : Coord, Adj (pair a b) (triple a b c) := by decide
 theorem triple_rotate : ∀ a b c : Coord, triple a b c=triple c a b := by decide
 theorem triple_swap : ∀ a b c : Coord, triple a b c=triple a c b := by decide
 theorem triple_cancel_left : ∀ a b : Coord, triple a b a=unit b := by decide
 theorem triple_cancel_right : ∀ a b : Coord, triple a b b=unit a := by decide
 theorem triple_injective_right : ∀ a b c d : Coord,
    triple a b c=triple a b d → c=d := by decide
 theorem triple_ne_unit : ∀ a b c : Coord, b≠c → triple a b c ≠ unit a := by decide

 def freshCoords (a b i : Coord) (k : Fin 4) : Coord :=
   ((List.finRange 9).filter (fun j => j != a && j != b && j != i))[k.val]!

 theorem freshCoords_spec : ∀ a b i : Coord,
     (∀ k : Fin 4, freshCoords a b i k ≠ a ∧ freshCoords a b i k ≠ b ∧ freshCoords a b i k ≠ i) ∧
     (∀ k l : Fin 4, freshCoords a b i k=freshCoords a b i l → k=l) := by decide

theorem triple_adj_sides : ∀ i j k : Coord,
    Adj (triple i j k) (pair i j) ∧ Adj (triple i j k) (pair i k) ∧
      Adj (triple i j k) (pair j k) := by decide

theorem three_pairs_distinct : ∀ i j k : Coord, i≠j → i≠k → j≠k →
    pair i j ≠ pair i k ∧ pair i j ≠ pair j k ∧ pair i k ≠ pair j k := by decide

#print axioms translate
#print axioms freshCoords_spec
end Snake9
