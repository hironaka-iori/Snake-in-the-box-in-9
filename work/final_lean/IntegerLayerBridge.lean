import Snake9
import Snake8

namespace IntegerLayerBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def encode (u : Snake8.Vertex × Bool) : Snake9.Vertex :=
  ⟨u.1.val + if u.2 then 256 else 0, by cases u.2 <;> simp <;> omega⟩

theorem encode_injective : ∀ u v, encode u = encode v → u = v := by
  rintro ⟨u,b⟩ ⟨v,c⟩ h
  have hv := congrArg Fin.val h
  cases b <;> cases c <;> simp only [encode, Bool.false_eq_true, ite_false, ite_true,
    Nat.add_zero, Fin.val_mk] at hv
  · have he : u = v := Fin.ext hv; simp [he]
  · omega
  · omega
  · have he : u = v := Fin.ext (by omega); simp [he]

theorem low_flip_table : ∀ u : Fin 256, ∀ k : Fin 8,
    Nat.xor (u.val + 256) (2^k.val) = Nat.xor u.val (2^k.val) + 256 ∧
    Nat.xor u.val (2^k.val) < 256 := by decide

theorem top_flip_table : ∀ u : Fin 256,
    Nat.xor u.val 256 = u.val + 256 ∧ Nat.xor (u.val + 256) 256 = u.val := by decide

theorem adj8_iff (u v : Snake8.Vertex) :
    Snake8.Adj u v ↔ ∃ k, k < 8 ∧ v.val = Nat.xor u.val (2^k) := by
  simp [Snake8.Adj, List.any_eq_true, List.mem_range]

theorem adjacency_bridge (u v : Snake8.Vertex × Bool) :
    Snake9.Adj (encode u) (encode v) ↔ LayerJoining.LayerAdj Snake8.Adj u v := by
  rcases u with ⟨u,b⟩
  rcases v with ⟨v,c⟩
  rw [Snake9.adj_iff_coordinate_flip]
  constructor
  · rintro ⟨k,hk,he⟩
    by_cases hlow : k < 8
    · obtain ⟨hflip,hbound⟩ := low_flip_table u ⟨k,hlow⟩
      simp only [Fin.val_mk] at hflip hbound
      cases b <;> cases c <;>
        simp only [encode, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero,
          Fin.val_mk] at he
      · exact Or.inl ⟨rfl,(adj8_iff u v).mpr ⟨k,hlow,he⟩⟩
      · omega
      · omega
      · have hval : v.val = Nat.xor u.val (2^k) := by omega
        exact Or.inl ⟨rfl,(adj8_iff u v).mpr ⟨k,hlow,hval⟩⟩
    · have h8 : k = 8 := by omega
      subst k
      obtain ⟨hfalse,htrue⟩ := top_flip_table u
      cases b <;> cases c <;>
        simp only [encode, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero,
          Fin.val_mk, show 2^8 = 256 from rfl] at he
      · omega
      · apply Or.inr
        constructor
        · change false ≠ true
          decide
        · change u = v
          apply Fin.ext
          omega
      · apply Or.inr
        constructor
        · change true ≠ false
          decide
        · change u = v
          apply Fin.ext
          omega
      · omega
  · intro h
    rcases h with ⟨he,hbase⟩ | ⟨hne,hbase⟩
    · have hbc : b = c := he
      subst c
      obtain ⟨k,hk,hval⟩ := (adj8_iff u v).mp hbase
      refine ⟨k,by omega,?_⟩
      obtain ⟨hflip,_⟩ := low_flip_table u ⟨k,hk⟩
      cases b <;> simp [encode, hval, hflip]
    · have huv : u = v := hbase
      subst v
      refine ⟨8,by decide,?_⟩
      obtain ⟨hfalse,htrue⟩ := top_flip_table u
      cases b <;> cases c <;> simp_all [encode]

def toSnake9 {m : Nat}
    (p : LayerJoining.InducedPath (Snake8.Vertex × Bool)
      (LayerJoining.LayerAdj Snake8.Adj) m) : Snake9.Snake m where
  vertex i := encode (p.vertex i)
  distinct i j h := p.distinct i j (encode_injective _ _ h)
  induced i j hij := (adjacency_bridge _ _).trans (p.induced i j hij)

def join {a b : Nat} (p : Snake8.Snake a) (q : Snake8.Snake b)
    (compatible : LayerJoining.Compatible p q) : Snake9.Snake (a+b+1) :=
  toSnake9 (LayerJoining.join p q compatible)

theorem compatible_98_97_gives_196 (p : Snake8.Snake 98) (q : Snake8.Snake 97)
    (compatible : LayerJoining.Compatible p q) : Nonempty (Snake9.Snake 196) :=
  ⟨join p q compatible⟩

theorem compatible_98_98_gives_197 (p q : Snake8.Snake 98)
    (compatible : LayerJoining.Compatible p q) : Nonempty (Snake9.Snake 197) :=
  ⟨join p q compatible⟩

theorem no197_excludes_compatible_98
    (h : ¬ Nonempty (Snake9.Snake 197)) (p q : Snake8.Snake 98) :
    ¬ LayerJoining.Compatible p q := by
  intro hc
  exact h (compatible_98_98_gives_197 p q hc)

theorem compatibility_iff_encoded_join_is_induced {a b : Nat}
    (p : Snake8.Snake a) (q : Snake8.Snake b) :
    LayerJoining.Compatible p q ↔
      (∀ i j : Fin (a+b+2), i.val < j.val →
        (Snake9.Adj (encode (LayerJoining.joinedVertex p q i))
          (encode (LayerJoining.joinedVertex p q j)) ↔ i.val+1=j.val)) := by
  constructor
  · intro hc i j hij
    exact (join p q hc).induced i j hij
  · intro h
    apply LayerJoining.compatibility_necessary p q
    intro i j hij
    exact (adjacency_bridge _ _).symm.trans (h i j hij)

#print axioms adjacency_bridge
#print axioms join
#print axioms compatible_98_97_gives_196
#print axioms compatible_98_98_gives_197
#print axioms no197_excludes_compatible_98
#print axioms compatibility_iff_encoded_join_is_induced
end IntegerLayerBridge
