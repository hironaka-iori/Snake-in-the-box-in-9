import Snake9

namespace Snake9
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def TerminalBlocked {m : Nat} (p : Snake m) : Prop :=
  ∀ w : Vertex, Adj (p.vertex ⟨m, by omega⟩) w →
    ∃ i : Fin m,
      p.vertex ⟨i.val, by omega⟩ = w ∨ Adj (p.vertex ⟨i.val, by omega⟩) w

def ExtendsRight {m : Nat} (p : Snake m) : Prop :=
  ∃ q : Snake (m + 1), ∀ i : Fin (m + 1), q.vertex ⟨i.val, by omega⟩ = p.vertex i

theorem blocked_prevents_extension {m : Nat} (p : Snake m)
    (hb : TerminalBlocked p) : ¬ ExtendsRight p := by
  rintro ⟨q, hq⟩
  have ha := (q.induced ⟨m, by omega⟩ ⟨m+1, by omega⟩
    (by change m < m+1; omega)).mpr rfl
  have he := hq ⟨m, by omega⟩
  rw [he] at ha
  obtain ⟨i, hi⟩ := hb (q.vertex ⟨m+1, by omega⟩) ha
  have hib := i.isLt
  have he := hq ⟨i.val, by omega⟩
  cases hi with
  | inl hi =>
    have h := q.distinct ⟨i.val, by omega⟩ ⟨m+1, by omega⟩ (he.trans hi)
    have hv := congrArg (fun z : Fin (m+1+1) => z.val) h
    change i.val = m+1 at hv
    omega
  | inr hi =>
    rw [← he] at hi
    have hv := (q.induced ⟨i.val, by omega⟩ ⟨m+1, by omega⟩
      (by change i.val < m+1; omega)).mp hi
    change i.val + 1 = m+1 at hv
    omega

def shortValues : Array Nat := #[0, 256, 320, 324, 340, 348, 349, 351, 95, 94, 30, 158, 414, 412, 408, 152, 184, 186, 170, 138, 139, 11, 267, 331, 330, 458, 450, 386, 390, 134, 6, 38, 34, 290, 354, 358, 366, 494, 492, 484, 228, 229, 101, 117, 53, 49, 57, 25, 29, 13, 5, 261, 263, 279, 311, 439, 183, 191, 175, 431, 399, 463, 461, 205, 204, 76, 72, 73, 65, 193, 192, 208, 80, 82, 18, 19, 147, 403, 467, 465, 497, 433, 441, 445, 509, 511, 507, 506, 504, 376, 360, 361, 353, 289]
def shortVertex (i : Fin 94) : Vertex :=
  ⟨shortValues[i.val]! % 512, Nat.mod_lt _ (by decide)⟩
theorem short_distinct : ∀ i j : Fin 94, shortVertex i = shortVertex j → i = j := by decide
theorem short_induced : ∀ i j : Fin 94, i.val < j.val →
    (Adj (shortVertex i) (shortVertex j) ↔ i.val + 1 = j.val) := by decide
def shortSnake : Snake 93 := ⟨shortVertex, short_distinct, short_induced⟩
def shortCandidate (k : Fin 9) : Vertex :=
  ⟨(Nat.xor 289 (2 ^ k.val)) % 512, Nat.mod_lt _ (by decide)⟩
def shortBlocker (k : Fin 9) : Fin 93 :=
  ⟨(#[1,33,51,91,45,1,91,81,45] : Array Nat)[k.val]! % 93, Nat.mod_lt _ (by decide)⟩
theorem short_candidate_value : ∀ k : Fin 9,
    (shortCandidate k).val = Nat.xor (shortSnake.vertex ⟨93, by decide⟩).val (2 ^ k.val) := by decide
theorem short_candidate_blockers : ∀ k : Fin 9,
    shortSnake.vertex ⟨(shortBlocker k).val, by omega⟩ = shortCandidate k ∨
    Adj (shortSnake.vertex ⟨(shortBlocker k).val, by omega⟩) (shortCandidate k) := by decide
theorem short_blocked : TerminalBlocked shortSnake := by
  intro w ha
  obtain ⟨k, hk, he⟩ := (adj_iff_coordinate_flip _ _).mp ha
  let a : Fin 9 := ⟨k,hk⟩
  have hw : w = shortCandidate a := by
    apply Fin.ext
    exact he.trans (short_candidate_value a).symm
  rw [hw]
  exact ⟨shortBlocker a, short_candidate_blockers a⟩

def shortReversedValues : Array Nat := #[289, 353, 361, 360, 376, 504, 506, 507, 511, 509, 445, 441, 433, 497, 465, 467, 403, 147, 19, 18, 82, 80, 208, 192, 193, 65, 73, 72, 76, 204, 205, 461, 463, 399, 431, 175, 191, 183, 439, 311, 279, 263, 261, 5, 13, 29, 25, 57, 49, 53, 117, 101, 229, 228, 484, 492, 494, 366, 358, 354, 290, 34, 38, 6, 134, 390, 386, 450, 458, 330, 331, 267, 11, 139, 138, 170, 186, 184, 152, 408, 412, 414, 158, 30, 94, 95, 351, 349, 348, 340, 324, 320, 256, 0]
def shortReversedVertex (i : Fin 94) : Vertex :=
  ⟨shortReversedValues[i.val]! % 512, Nat.mod_lt _ (by decide)⟩
theorem shortReversed_distinct : ∀ i j : Fin 94, shortReversedVertex i = shortReversedVertex j → i = j := by decide
theorem shortReversed_induced : ∀ i j : Fin 94, i.val < j.val →
    (Adj (shortReversedVertex i) (shortReversedVertex j) ↔ i.val + 1 = j.val) := by decide
def shortReversedSnake : Snake 93 := ⟨shortReversedVertex, shortReversed_distinct, shortReversed_induced⟩
def shortReversedCandidate (k : Fin 9) : Vertex :=
  ⟨(Nat.xor 0 (2 ^ k.val)) % 512, Nat.mod_lt _ (by decide)⟩
def shortReversedBlocker (k : Fin 9) : Fin 93 :=
  ⟨(#[25,19,43,27,19,61,21,23,91] : Array Nat)[k.val]! % 93, Nat.mod_lt _ (by decide)⟩
theorem shortReversed_candidate_value : ∀ k : Fin 9,
    (shortReversedCandidate k).val = Nat.xor (shortReversedSnake.vertex ⟨93, by decide⟩).val (2 ^ k.val) := by decide
theorem shortReversed_candidate_blockers : ∀ k : Fin 9,
    shortReversedSnake.vertex ⟨(shortReversedBlocker k).val, by omega⟩ = shortReversedCandidate k ∨
    Adj (shortReversedSnake.vertex ⟨(shortReversedBlocker k).val, by omega⟩) (shortReversedCandidate k) := by decide
theorem shortReversed_blocked : TerminalBlocked shortReversedSnake := by
  intro w ha
  obtain ⟨k, hk, he⟩ := (adj_iff_coordinate_flip _ _).mp ha
  let a : Fin 9 := ⟨k,hk⟩
  have hw : w = shortReversedCandidate a := by
    apply Fin.ext
    exact he.trans (shortReversed_candidate_value a).symm
  rw [hw]
  exact ⟨shortReversedBlocker a, shortReversed_candidate_blockers a⟩

theorem reverse_matches : ∀ i : Fin 94,
    shortReversedSnake.vertex i = shortSnake.vertex ⟨93-i.val, by omega⟩ := by decide

theorem short_cannot_extend_either_end :
    ¬ ExtendsRight shortSnake ∧ ¬ ExtendsRight shortReversedSnake :=
  ⟨blocked_prevents_extension shortSnake short_blocked,
   blocked_prevents_extension shortReversedSnake shortReversed_blocked⟩

theorem endpoint_maximality_does_not_prove_maximum :
    (¬ ExtendsRight shortSnake ∧ ¬ ExtendsRight shortReversedSnake) ∧
    Nonempty (Snake 191) ∧ 93 < 191 :=
  ⟨short_cannot_extend_either_end, lower_bound, by decide⟩

#print axioms short_cannot_extend_either_end
#print axioms reverse_matches
#print axioms endpoint_maximality_does_not_prove_maximum
end Snake9
