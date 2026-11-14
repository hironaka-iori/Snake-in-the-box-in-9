import ConcreteGeometry213

/-!
Source prepared for checking; not compiled by its author.
The actual-path premise uses the literal retained coordinates and groups.
The conclusions supply raw-Nat distinctness and partner completeness.
Alphabet membership, domains, native masks, and traversal are separate.
-/

namespace ConcreteSupport213

open ConcreteGeometry213 IndexedCriterion206

def word (u : Nat) : List Bool :=
  (List.range 6).map (fun k => u.testBit k)

theorem consecutive_groups :
    ∀ i j : Fin 99, i.val < j.val → j.val = i.val + 1 →
      group j = group i ∨ group j = group i + 1 := by
  intro i j _ hnext
  have hi : i.val < 98 := by
    have hj := j.isLt
    omega
  have h := List.all_eq_true.mp consecutive_groups_data
    i.val (List.mem_range.mpr hi)
  have hd :
      groups[i.val + 1]! = groups[i.val]! ∨
      groups[i.val + 1]! = groups[i.val]! + 1 := by
    simpa using h
  simpa [group, hnext] using hd

/-- Every required literal pair has unequal raw assigned words whenever
the reconstructed indexed vertices constitute an induced Q8 path. -/
theorem required_words_ne (values : Nat → Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ word (values (group i))))
    (x y : Nat) (hxy : (x,y) ∈ requiredPairs) :
    values x ≠ values y := by
  have hm :
      (x,y) ∈ certificates.map (fun c => (c.1,c.2.1)) := by
    rw [certificate_coverage]
    exact hxy
  obtain ⟨c, hc, hpair⟩ := List.mem_map.mp hm
  rcases c with ⟨a,b,i,j⟩
  have hv := List.all_eq_true.mp certificate_validity (a,b,i,j) hc
  have hdata :
      i < 99 ∧ j < 99 ∧ groups[i]! = a ∧ groups[j]! = b ∧
      a ≠ b ∧ a % 2 = b % 2 ∧
      baseRaw i ≠ Square209.opposite (baseRaw j) := by
    simpa only [validCertificate, decide_eq_true_eq] using hv
  rcases hdata with ⟨hi,hj,hgi,hgj,hne,hpar,hbase⟩
  have hab : a = x ∧ b = y := Prod.mk.inj hpair
  let fi : Fin 99 := ⟨i,hi⟩
  let fj : Fin 99 := ⟨j,hj⟩
  have hconf := IntervalGeometry213.shared_word_conflict
    (r := 6) z group (fun g => word (values g)) hp consecutive_groups fi fj
    (by simpa [group, fi, fj, hgi, hgj] using hne)
    (by simpa [group, fi, fj, hgi, hgj] using hpar)
    (by simpa [z, fi, fj] using hbase)
  have hdecoded : word (values x) ≠ word (values y) := by
    simpa [group, fi, fj, hgi, hgj, hab.1, hab.2] using hconf
  intro heq
  exact hdecoded (congrArg word heq)

private theorem mem_within (xs : List Nat) (x y : Nat)
    (hx : x ∈ xs) (hy : y ∈ xs) (hxy : x < y) :
    (x,y) ∈ withinPairs xs := by
  apply List.mem_flatMap.mpr
  refine ⟨x, hx, ?_⟩
  apply List.mem_map.mpr
  exact ⟨y, by simpa using And.intro hy hxy, rfl⟩

private theorem mapped_distinct (xs : List Nat) (values : Nat → Nat)
    (hxs : xs.Nodup)
    (hpairs : ∀ x y, (x,y) ∈ withinPairs xs → values x ≠ values y) :
    (xs.map values).Nodup := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem ?_ hxs
  intro a b ha hb hne
  by_cases hab : a < b
  · exact hpairs a b (mem_within xs a b ha hb hab)
  · have hba : b < a := by omega
    exact Ne.symm (hpairs b a (mem_within xs b a hb ha hba))

private theorem family_conditions (C O : List Nat) (values : Nat → Nat)
    (hC : C.Nodup) (hO : O.Nodup)
    (hpairs : ∀ x y, (x,y) ∈ familyPairs C O → values x ≠ values y) :
    (C.map values).Nodup ∧ (O.map values).Nodup ∧
    (∀ i, i ∈ O → ∀ c, c ∈ C →
      values c = values i → c ∈ partners i) := by
  refine ⟨?_, ?_, ?_⟩
  · apply mapped_distinct C values hC
    intro x y h
    apply hpairs x y
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))
  · apply mapped_distinct O values hO
    intro x y h
    apply hpairs x y
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
  · intro i hi c hc heq
    by_cases hp : c ∈ partners i
    · exact hp
    · have hm :
          (i,c) ∈ O.flatMap
            (fun x => (C.filter (fun y => !(partners x).contains y)).map
              (fun y => (x,y))) := by
        apply List.mem_flatMap.mpr
        refine ⟨i, hi, ?_⟩
        apply List.mem_map.mpr
        exact ⟨c, by simp [hc, hp], rfl⟩
      have hne := hpairs i c (List.mem_append.mpr (Or.inr hm))
      exact False.elim (hne heq.symm)

/-- The chosen and outside even families have distinct assigned words,
and every actual sharer in the chosen family is a listed partner. -/
theorem even_support_conditions (values : Nat → Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ word (values (group i)))) :
    (chosen0.map values).Nodup ∧ (outside0.map values).Nodup ∧
    (∀ i, i ∈ outside0 → ∀ c, c ∈ chosen0 →
      values c = values i → c ∈ partners i) := by
  apply family_conditions chosen0 outside0 values
    (by decide +kernel) (by decide +kernel)
  intro x y h
  apply required_words_ne values hp x y
  exact List.mem_append.mpr (Or.inl h)

/-- The corresponding source-specific implications for the odd families. -/
theorem odd_support_conditions (values : Nat → Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ word (values (group i)))) :
    (chosen1.map values).Nodup ∧ (outside1.map values).Nodup ∧
    (∀ i, i ∈ outside1 → ∀ c, c ∈ chosen1 →
      values c = values i → c ∈ partners i) := by
  apply family_conditions chosen1 outside1 values
    (by decide +kernel) (by decide +kernel)
  intro x y h
  apply required_words_ne values hp x y
  exact List.mem_append.mpr (Or.inr h)

#print axioms consecutive_groups
#print axioms required_words_ne
#print axioms even_support_conditions
#print axioms odd_support_conditions

end ConcreteSupport213
