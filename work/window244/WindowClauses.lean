import WindowCounters
import LocalRup

namespace Snake9.Window244
noncomputable section
local instance propDecClause (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0

/-- Semantic descriptors, independent of the numbering chosen by an encoder. -/
inductive Atom where
  | selected (v : Vertex)
  | endpoint (v : Vertex)
  | endpointThreshold (vs : List Vertex) (k : Nat)
  | missingThreshold (vs : List Vertex) (k : Nat)
  | constant (b : Bool)
  deriving DecidableEq

def Atom.meaning {m : Nat} (p : Snake m) : Atom → Prop
  | .selected v => InPath p v
  | .endpoint v => BallClauseLogic.Endpoint p v
  | .endpointThreshold vs k => k ≤ endpointCount p vs
  | .missingThreshold vs k => k ≤ missingCount p vs
  | .constant b => b = true

abbrev SemanticLit := Atom × Bool
def litHolds {m : Nat} (p : Snake m) (l : SemanticLit) : Prop :=
  if l.2 then l.1.meaning p else ¬ l.1.meaning p
def holds {m : Nat} (p : Snake m) : List SemanticLit → Prop
  | [] => False
  | l::ls => litHolds p l ∨ holds p ls

/-- The assignment is fully determined by the descriptor table. -/
def assignment {m : Nat} (p : Snake m) (decode : Nat → Atom) (i : Nat) : Bool :=
  decide ((decode i).meaning p)

theorem numbered_clause_iff {m : Nat} (p : Snake m) (decode : Nat → Atom)
    (c : List LocalRup.Lit) :
    LocalRup.clause (assignment p decode) c = true ↔
      holds p (c.map (fun l => (decode l.1,l.2))) := by
  induction c with
  | nil => simp [LocalRup.clause,holds]
  | cons l ls ih =>
    rcases l with ⟨n,b⟩
    cases b <;> simp [LocalRup.clause,LocalRup.value,assignment,holds,litHolds] at ih ⊢ <;> exact or_congr Iff.rfl ih

theorem holds_of_mem {m : Nat} (p : Snake m) (c : List SemanticLit) (l : SemanticLit)
    (hm : l ∈ c) (hl : litHolds p l) : holds p c := by
  induction c with
  | nil => contradiction
  | cons a c ih =>
    rcases List.mem_cons.mp hm with rfl | h
    · exact Or.inl hl
    · exact Or.inr (ih h)

theorem selected_clause {m : Nat} (p : Snake m) (v : Vertex) (hv : InPath p v) :
    holds p [(.selected v,true)] := by
  simpa [holds,litHolds,Atom.meaning] using hv

theorem degree_family {m : Nat} (p : Snake m) (v a b c : Vertex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hva : Adj v a) (hvb : Adj v b) (hvc : Adj v c) :
    holds p [(.selected v,false),(.selected a,false),(.selected b,false),(.selected c,false)] := by
  simpa [holds,litHolds,Atom.meaning] using BallClauseLogic.degree_clause p v a b c hab hac hbc hva hvb hvc

theorem endpoint_selected_family {m : Nat} (p : Snake m) (v : Vertex) :
    holds p [(.endpoint v,false),(.selected v,true)] := by
  by_cases h : BallClauseLogic.Endpoint p v
  · exact Or.inr (Or.inl h.1)
  · exact Or.inl h

theorem endpoint_degree_family {m : Nat} (p : Snake m) (v a b : Vertex)
    (hab : a ≠ b) (hva : Adj v a) (hvb : Adj v b) :
    holds p [(.endpoint v,false),(.selected a,false),(.selected b,false)] := by
  simpa [holds,litHolds,Atom.meaning] using BallClauseLogic.endpoint_degree_clause p v a b hab hva hvb

theorem cycle_family {m : Nat} (p : Snake m) (vs : List Vertex) (hne : vs ≠ [])
    (hd : ∀ v ∈ vs, ∃ a ∈ vs, ∃ b ∈ vs, a ≠ b ∧ Adj v a ∧ Adj v b) :
    holds p (vs.map (fun v => (.selected v,false))) := by
  classical
  apply Classical.byContradiction
  intro h
  apply selected_no_cycle p vs hne hd
  intro v hv
  apply Classical.byContradiction
  intro hn
  apply h
  apply holds_of_mem p _ (.selected v,false)
  · exact List.mem_map.mpr ⟨v,hv,rfl⟩
  · exact hn

theorem positive_degree_family {m : Nat} (p : Snake m) (hm : 0 < m) (v : Vertex)
    (ns : List Vertex) (hc : ∀ w, Adj v w → w ∈ ns) :
    holds p ((.selected v,false)::ns.map (fun w => (.selected w,true))) := by
  rcases neighbor_cover p hm v ns (fun w _ h => hc w h) with hn | ⟨w,hw,hp⟩
  · exact Or.inl hn
  · apply Or.inr
    exact holds_of_mem p _ (.selected w,true) (List.mem_map.mpr ⟨w,hw,rfl⟩) hp

theorem degree_one_endpoint_family {m : Nat} (p : Snake m) (v excluded : Vertex)
    (ns : List Vertex) (hc : ∀ w, Adj v w → w ≠ excluded → w ∈ ns) :
    holds p ((.selected v,false)::(.endpoint v,true)::ns.map (fun w => (.selected w,true))) := by
  rcases other_cover p v excluded ns (fun w _ h hn => hc w h hn) with hn | he | ⟨w,hw,hp⟩
  · exact Or.inl hn
  · exact Or.inr (Or.inl he)
  · apply Or.inr; apply Or.inr
    exact holds_of_mem p _ (.selected w,true) (List.mem_map.mpr ⟨w,hw,rfl⟩) hp

/-- Simplifying a false constant literal preserves the clause. This is the
only simplification required for retained missing-counter clauses. -/
theorem constant_false_cons {m : Nat} (p : Snake m) (b : Bool) (ls : List SemanticLit) :
    holds p ((.constant b,!b)::ls) ↔ holds p ls := by
  cases b <;> simp [holds,litHolds,Atom.meaning]

theorem endpoint_counter_family {m : Nat} (p : Snake m) (vs : List Vertex)
    (v : Vertex) (hn : (vs ++ [v]).Nodup) :
    holds p [(.endpoint v,false),(.endpointThreshold (vs++[v]) 1,true)] ∧
    holds p [(.endpointThreshold vs 1,false),(.endpointThreshold (vs++[v]) 1,true)] ∧
    holds p [(.endpointThreshold vs 2,false),(.endpointThreshold (vs++[v]) 2,true)] ∧
    holds p [(.endpoint v,false),(.endpointThreshold vs 1,false),(.endpointThreshold (vs++[v]) 2,true)] ∧
    holds p [(.endpoint v,false),(.endpointThreshold vs 2,false)] := by
  simpa [holds,litHolds,Atom.meaning] using endpoint_counter_clauses p vs v hn

theorem missing_counter_family {m : Nat} (p : Snake m) (vs : List Vertex)
    (v : Vertex) (j : Nat) (hj : 0 < j) :
    holds p [(.missingThreshold vs j,false),(.missingThreshold (vs++[v]) j,true)] ∧
    holds p [(.selected v,true),(.missingThreshold vs (j-1),false),(.missingThreshold (vs++[v]) j,true)] ∧
    holds p [(.missingThreshold (vs++[v]) j,false),(.missingThreshold vs j,true),(.selected v,false)] ∧
    holds p [(.missingThreshold (vs++[v]) j,false),(.missingThreshold vs j,true),(.missingThreshold vs (j-1),true)] := by
  simpa [holds,litHolds,Atom.meaning] using missing_counter_clauses p vs v j hj

theorem missing_exact_family {m : Nat} (p : Snake m) (vs : List Vertex) (k : Nat)
    (hk : missingCount p vs = k) :
    holds p [(.missingThreshold vs k,true)] ∧
    holds p [(.missingThreshold vs (k+1),false)] := by
  simpa [holds,litHolds,Atom.meaning] using missing_exact_clauses p vs k hk

def staticValue : Atom → Option Bool
  | .constant b => some b
  | .endpointThreshold _ 0 => some true
  | .missingThreshold _ 0 => some true
  | .endpointThreshold [] (_+1) => some false
  | .missingThreshold [] (_+1) => some false
  | _ => none

theorem staticValue_sound {m : Nat} (p : Snake m) (a : Atom) (b : Bool)
    (h : staticValue a = some b) : a.meaning p ↔ b = true := by
  cases a with
  | selected v => simp [staticValue] at h
  | endpoint v => simp [staticValue] at h
  | constant c => simp [staticValue] at h; subst b; rfl
  | endpointThreshold vs k =>
    cases k with
    | zero => simp [staticValue] at h; subst b; simp [Atom.meaning]
    | succ k => cases vs <;> simp [staticValue] at h
                subst b; simp [Atom.meaning,endpointCount]
  | missingThreshold vs k =>
    cases k with
    | zero => simp [staticValue] at h; subst b; simp [Atom.meaning]
    | succ k => cases vs <;> simp [staticValue] at h
                subst b; simp [Atom.meaning,missingCount]

def reduceConstants : List SemanticLit → List SemanticLit
  | [] => []
  | (a,s)::ls => match staticValue a with
    | none => (a,s)::reduceConstants ls
    | some b => if b == s then [(.constant true,true)] else reduceConstants ls

theorem reduceConstants_iff {m : Nat} (p : Snake m) (c : List SemanticLit) :
    holds p (reduceConstants c) ↔ holds p c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    rcases l with ⟨a,s⟩
    cases h : staticValue a with
    | none => simp [reduceConstants,h,holds,ih]
    | some b =>
      have hb := staticValue_sound p a b h
      cases b <;> cases s <;> simp [reduceConstants,h,holds,litHolds,hb,ih] <;> simp [Atom.meaning]

/-- Finite equality of decoded clause data connects an encoder's numbering to
the generic family proofs; no generator is part of the trusted base. -/
theorem numbered_of_family {m : Nat} (p : Snake m) (decode : Nat → Atom)
    (c : List LocalRup.Lit) (expected : List SemanticLit)
    (he : c.map (fun l => (decode l.1,l.2)) = reduceConstants expected)
    (hs : holds p expected) : LocalRup.clause (assignment p decode) c = true := by
  apply (numbered_clause_iff p decode c).mpr
  rw [he]
  exact (reduceConstants_iff p expected).mpr hs

#print axioms numbered_clause_iff
#print axioms degree_family
#print axioms endpoint_selected_family
#print axioms endpoint_degree_family
#print axioms cycle_family
#print axioms positive_degree_family
#print axioms degree_one_endpoint_family
#print axioms constant_false_cons
#print axioms endpoint_counter_family
#print axioms missing_counter_family
#print axioms missing_exact_family
#print axioms reduceConstants_iff
#print axioms numbered_of_family
end
end Snake9.Window244
