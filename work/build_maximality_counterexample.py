import json
from pathlib import Path

vs=json.loads(Path('outputs/short_maximal_witness.json').read_text())['vertex_sequence']
assert len(vs)==94
text='''import Snake9

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
'''
for name,values in [('short',vs),('shortReversed',vs[::-1])]:
    end=values[-1]
    blockers=[next(i for i,v in enumerate(values[:-1]) if v==(end^(1<<k)) or (v^(end^(1<<k))).bit_count()==1) for k in range(9)]
    text+=f'''
def {name}Values : Array Nat := #[{', '.join(map(str,values))}]
def {name}Vertex (i : Fin 94) : Vertex :=
  ⟨{name}Values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩
theorem {name}_distinct : ∀ i j : Fin 94, {name}Vertex i = {name}Vertex j → i = j := by decide
theorem {name}_induced : ∀ i j : Fin 94, i.val < j.val →
    (Adj ({name}Vertex i) ({name}Vertex j) ↔ i.val + 1 = j.val) := by decide
def {name}Snake : Snake 93 := ⟨{name}Vertex, {name}_distinct, {name}_induced⟩
def {name}Candidate (k : Fin 9) : Vertex :=
  ⟨(Nat.xor {end} (2 ^ k.val)) % 512, Nat.mod_lt _ (by decide)⟩
def {name}Blocker (k : Fin 9) : Fin 93 :=
  ⟨(#[{','.join(map(str,blockers))}] : Array Nat)[k.val]! % 93, Nat.mod_lt _ (by decide)⟩
theorem {name}_candidate_value : ∀ k : Fin 9,
    ({name}Candidate k).val = Nat.xor ({name}Snake.vertex ⟨93, by decide⟩).val (2 ^ k.val) := by decide
theorem {name}_candidate_blockers : ∀ k : Fin 9,
    {name}Snake.vertex ⟨({name}Blocker k).val, by omega⟩ = {name}Candidate k ∨
    Adj ({name}Snake.vertex ⟨({name}Blocker k).val, by omega⟩) ({name}Candidate k) := by decide
theorem {name}_blocked : TerminalBlocked {name}Snake := by
  intro w ha
  obtain ⟨k, hk, he⟩ := (adj_iff_coordinate_flip _ _).mp ha
  let a : Fin 9 := ⟨k,hk⟩
  have hw : w = {name}Candidate a := by
    apply Fin.ext
    exact he.trans ({name}_candidate_value a).symm
  rw [hw]
  exact ⟨{name}Blocker a, {name}_candidate_blockers a⟩
'''
text+='''
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
'''
Path('outputs/MaximalityCounterexample.lean').write_text(text,encoding='utf-8')
