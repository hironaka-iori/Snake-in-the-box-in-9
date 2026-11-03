import Std

/- A snake's length is its number of edges. No optimality axiom is declared. -/
namespace Snake9

abbrev Vertex := Fin 512

def Adj (u v : Vertex) : Prop :=
  (List.range 9).any (fun k => v.val == Nat.xor u.val (2 ^ k)) = true

instance (u v : Vertex) : Decidable (Adj u v) :=
  inferInstanceAs (Decidable (_ = true))

theorem adj_iff_coordinate_flip (u v : Vertex) :
    Adj u v ↔ ∃ k : Nat, k < 9 ∧ v.val = Nat.xor u.val (2 ^ k) := by
  simp [Adj, List.any_eq_true]

structure Snake (m : Nat) where
  vertex : Fin (m + 1) → Vertex
  distinct : ∀ i j, vertex i = vertex j → i = j
  induced : ∀ i j, i.val < j.val → (Adj (vertex i) (vertex j) ↔ i.val + 1 = j.val)

def takePrefix {m k : Nat} (p : Snake m) (h : k ≤ m) : Snake k where
  vertex i := p.vertex ⟨i.val, by omega⟩
  distinct i j eq := by
    have e := p.distinct ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ eq
    apply Fin.ext
    exact congrArg (fun x : Fin (m + 1) => x.val) e
  induced i j hij := p.induced ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij

theorem no192_iff_upperBound :
    (¬ Nonempty (Snake 192)) ↔ (∀ m, Nonempty (Snake m) → m ≤ 191) := by
  constructor
  · intro h m hp
    cases Nat.lt_or_ge m 192 with
    | inl hm => omega
    | inr hm =>
      obtain ⟨p⟩ := hp
      exact False.elim (h ⟨takePrefix p hm⟩)
  · intro h hp
    have := h 192 hp
    omega

/- An exact finite target: 193 distinct cube vertices in induced-path order. -/
def Target192 : Prop :=
  ∃ f : Fin 193 → Vertex,
    (∀ i j, f i = f j → i = j) ∧
    (∀ i j, i.val < j.val → (Adj (f i) (f j) ↔ i.val + 1 = j.val))

theorem target192_iff : Target192 ↔ Nonempty (Snake 192) := by
  constructor
  · rintro ⟨f, hd, hi⟩
    exact ⟨⟨f, hd, hi⟩⟩
  · rintro ⟨p⟩
    exact ⟨p.vertex, p.distinct, p.induced⟩

theorem target192_impossible_iff_upperBound :
    (¬ Target192) ↔ (∀ m, Nonempty (Snake m) → m ≤ 191) := by
  rw [target192_iff, no192_iff_upperBound]

#print axioms no192_iff_upperBound
#print axioms target192_impossible_iff_upperBound

-- BEGIN WITNESS
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def witnessValues : Array Nat := #[0, 1, 3, 7, 6, 14, 12, 28, 60, 61, 125, 121, 123, 122, 58, 26, 27, 31, 95, 87, 85, 69, 77, 73, 75, 74, 66, 98, 99, 103, 111, 47, 43, 41, 40, 104, 108, 100, 36, 37, 165, 181, 180, 244, 252, 248, 184, 185, 187, 191, 255, 247, 243, 242, 178, 162, 418, 426, 427, 431, 495, 487, 485, 453, 461, 457, 393, 385, 387, 391, 390, 398, 462, 458, 450, 466, 467, 471, 479, 415, 411, 410, 408, 472, 476, 468, 404, 405, 277, 309, 308, 372, 380, 376, 312, 313, 315, 319, 383, 375, 371, 370, 306, 274, 278, 286, 350, 346, 347, 345, 337, 321, 323, 327, 326, 324, 332, 328, 264, 266, 267, 271, 269, 301, 365, 361, 363, 362, 366, 302, 294, 295, 291, 289, 288, 352, 480, 496, 432, 433, 435, 439, 438, 502, 510, 506, 507, 505, 509, 445, 444, 428, 172, 174, 238, 234, 235, 233, 225, 193, 195, 199, 198, 196, 204, 200, 136, 138, 139, 143, 141, 157, 221, 217, 219, 218, 222, 158, 150, 151, 147, 145, 144, 208, 80, 112, 48, 49, 51, 55, 54, 118]

def witnessVertex (i : Fin 192) : Vertex :=
  ⟨witnessValues[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem witness_distinct :
    ∀ i j : Fin 192, witnessVertex i = witnessVertex j → i = j := by decide

theorem witness_induced :
    ∀ i j : Fin 192, i.val < j.val →
      (Adj (witnessVertex i) (witnessVertex j) ↔ i.val + 1 = j.val) := by decide

def witness : Snake 191 := ⟨witnessVertex, witness_distinct, witness_induced⟩

theorem lower_bound : Nonempty (Snake 191) := ⟨witness⟩

theorem optimality_of_no192 (h : ¬ Target192) :
    Nonempty (Snake 191) ∧ (∀ m, Nonempty (Snake m) → m ≤ 191) :=
  ⟨lower_bound, target192_impossible_iff_upperBound.mp h⟩

#print axioms witness_distinct
#print axioms witness_induced
#print axioms lower_bound
#print axioms optimality_of_no192
end Snake9
