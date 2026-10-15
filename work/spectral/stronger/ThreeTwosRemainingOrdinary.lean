import NormalizeDistinctThreeTwos
import CommonHoleExclusion
import StarOuterExclusion

namespace Snake9
open Finset Classical
noncomputable section

theorem pair_supported_insert_cases (s R : Finset Coord) (x : Coord)
    (hs : s.card=2) (hsub : s⊆insert x R) :
    s⊆R ∨ ∃y,y∈R ∧ y≠x ∧ s={x,y} := by
  by_cases hx : x∈s
  · obtain ⟨i,j,hij,hsij⟩ := Finset.card_eq_two.mp hs
    rw [hsij] at hx
    rcases Finset.mem_insert.mp hx with he | he
    · subst i
      have hjR : j∈R := (Finset.mem_insert.mp (hsub (by rw [hsij]; simp))).resolve_left (Ne.symm hij)
      exact Or.inr ⟨j,hjR,Ne.symm hij,hsij⟩
    · have he' : x=j := Finset.mem_singleton.mp he
      subst j
      have hiR : i∈R := (Finset.mem_insert.mp (hsub (by rw [hsij]; simp))).resolve_left hij
      exact Or.inr ⟨i,hiR,hij,by rw [hsij]; exact Finset.pair_comm _ _⟩
  · exact Or.inl (fun y hy => (Finset.mem_insert.mp (hsub hy)).resolve_left (fun he => hx (he ▸ hy)))

/-- All already excluded branches are removed; at least one remaining outer edge is ordinary. -/
theorem DistinctOuterConfig.remaining_ordinary_case {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : DistinctOuterConfig p a b c d) (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) :
    ∃s t : Finset Coord,s.card=2 ∧ t.card=2 ∧
      s⊆insert d (distinctR a b c d) ∧ t⊆insert c (distinctR a b c d) ∧
      b∉s ∧ a∉t ∧ h.left.F=insert {b,d} {s} ∧ h.right.F=insert {a,c} {t} ∧
      (s⊆distinctR a b c d ∨ t⊆distinctR a b c d) := by
  rcases h.remaining_double_delta_cases f hFcard with ⟨e,he,hl,hr⟩ | ⟨s,t,hs,ht,hsR,htR,hbs,hat,hl,hr⟩
  · let ch : CommonHoleConfig p a b c d := ⟨h,e,(mem_distinctR a b c d e).mp he,hl,hr⟩
    exact False.elim (ch.impossible f hFcard)
  · refine ⟨s,t,hs,ht,hsR,htR,hbs,hat,hl,hr,?_⟩
    rcases pair_supported_insert_cases s (distinctR a b c d) d hs hsR with hsR' | ⟨e,he,hed,heq⟩
    · exact Or.inl hsR'
    rcases pair_supported_insert_cases t (distinctR a b c d) c ht htR with htR' | ⟨g,hg,hgc,hgq⟩
    · exact Or.inr htR'
    let sh : StarOuterConfig p a b c d :=
      ⟨h,e,g,he,hg,by simpa only [heq] using hl,by simpa only [hgq] using hr⟩
    exact False.elim (sh.impossible f hFcard)

#print axioms DistinctOuterConfig.remaining_ordinary_case
end
end Snake9
