import ParallelShareClauses
import LocalWindowTags

/-! Full parallel-share certificate interface. A successful data check proves
all clause families under one assignment, including the old endpoint counters. -/
namespace Snake9.ParallelShareCertificate
open Snake9.LocalWindow Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareBoolean

def compatible (oldM : Tags.MT) (M : Nat → Option Meaning) (x : Nat) : Bool :=
  match M x with
  | none => true
  | some (.boolean (.sel v)) => match oldM.get x with
    | .p u => v == u
    | _ => false
  | _ => false

theorem compatible_sem (S E : Nat → Bool) (oldM : Tags.MT) (ctrs : List Tags.Ctr)
    (ts : List Term) (M : Nat → Option Meaning) (x : Nat) (h : compatible oldM M x = true) :
    ParallelShareClauses.assignment (Tags.tau S E oldM ctrs) S ts M x = Tags.tau S E oldM ctrs x := by
  unfold compatible at h
  split at h
  · rename_i hm
    simp [ParallelShareClauses.assignment, hm]
  · rename_i v hm
    split at h
    · rename_i u hu
      simp only [beq_iff_eq] at h
      simp [ParallelShareClauses.assignment, hm, Formula.eval, Tags.tau, hu, h]
    · simp at h
  · simp at h

theorem compatible_clause (S E : Nat → Bool) (oldM : Tags.MT) (ctrs : List Tags.Ctr)
    (ts : List Term) (M : Nat → Option Meaning) (cl : List Nat)
    (hc : cl.all (fun a => decide (2 ≤ a) && compatible oldM M (a / 2)) = true)
    (h : clauseTrue (Tags.tau S E oldM ctrs) (cl.map decodeLit) = true) :
    clauseTrue (ParallelShareClauses.assignment (Tags.tau S E oldM ctrs) S ts M)
      (cl.map decodeLit) = true := by
  unfold clauseTrue at h ⊢
  rw [List.any_map, List.any_eq_true] at h ⊢
  obtain ⟨a, ha, hv⟩ := h
  refine ⟨a, ha, ?_⟩
  have hp := List.all_eq_true.mp hc a ha
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  simp only [Function.comp] at hv ⊢
  rw [Tags.decode_eq _ hp.1] at hv ⊢
  unfold Tags.lv
  rw [compatible_sem S E oldM ctrs ts M _ hp.2]
  exact hv

def sublist : List Term → List Term → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: xs, b :: ys => if a = b then sublist xs ys else sublist (a :: xs) ys

theorem sublist_sound : ∀ {xs ys : List Term}, sublist xs ys = true → xs.Sublist ys
  | [], _, _ => List.nil_sublist _
  | _ :: _, [], h => by simp [sublist] at h
  | a :: xs, b :: ys, h => by
    by_cases he : a = b
    · subst b; simp only [sublist, if_true] at h; exact (sublist_sound h).cons₂ a
    · simp only [sublist, he, if_false] at h; exact (sublist_sound h).cons b

inductive Tag where
  | old (tag : Tags.Tag)
  | boolean
  | merge (left right : Ref)
  | bound

def checkClause (oldM : Tags.MT) (ctrs : List Tags.Ctr) (w : List Nat) (ts : List Term)
    (M : Nat → Option Meaning) (cap : Nat) : Tag → List Nat → Bool
  | .old tag, cl => Tags.ckClause oldM ctrs w tag cl &&
      cl.all (fun a => decide (2 ≤ a) && compatible oldM M (a / 2))
  | .boolean, cl => ParallelShareBoolean.checkClause 8 w (booleanMeaning M) (cl.map decodeLit)
  | .merge a b, cl => mergeCheck w ts M a b (cl.map decodeLit)
  | .bound, cl => boundCheck cap M (cl.map decodeLit)

theorem clause_sound {S E : Nat → Bool} {w : List Nat} {cs : List Centre} {cap : Nat}
    (ax : AxiomsP S E w cs cap) (oldM : Tags.MT) (ctrs : List Tags.Ctr)
    (hctrs : ctrs.all (Tags.ctrOK oldM cs) = true)
    (ts : List Term) (ht : ts.Sublist (allTerms cs)) (M : Nat → Option Meaning)
    (tag : Tag) (cl : List Nat) (h : checkClause oldM ctrs w ts M cap tag cl = true) :
    clauseTrue (ParallelShareClauses.assignment (Tags.tau S E oldM ctrs) S ts M)
      (cl.map decodeLit) = true := by
  cases tag with
  | old tag =>
    simp only [checkClause, Bool.and_eq_true] at h
    exact compatible_clause S E oldM ctrs ts M cl h.2 (Tags.sound_clause h.1 hctrs ax.toAxioms)
  | boolean => exact boolean_clause _ S ts M w _ h ax.window_sel
  | merge a b => exact mergeCheck_sound ax.toAxioms ts M a b _ h
  | bound => exact boundCheck_sound ax ts ht M _ h

def checkRaw (oldM : Tags.MT) (ctrs : List Tags.Ctr) (w : List Nat) (ts : List Term)
    (M : Nat → Option Meaning) (cap : Nat) : List Tag → List (List Nat) → Bool
  | [], [] => true
  | t :: tags, cl :: cls => checkClause oldM ctrs w ts M cap t cl &&
      checkRaw oldM ctrs w ts M cap tags cls
  | _, _ => false

theorem raw_sound {S E : Nat → Bool} {w : List Nat} {cs : List Centre} {cap : Nat}
    (ax : AxiomsP S E w cs cap) (oldM : Tags.MT) (ctrs : List Tags.Ctr)
    (hctrs : ctrs.all (Tags.ctrOK oldM cs) = true)
    (ts : List Term) (ht : ts.Sublist (allTerms cs)) (M : Nat → Option Meaning) :
    ∀ (tags : List Tag) (raw : List (List Nat)), checkRaw oldM ctrs w ts M cap tags raw = true →
      cnfTrue (ParallelShareClauses.assignment (Tags.tau S E oldM ctrs) S ts M)
        (raw.map (List.map decodeLit)) = true
  | [], [], _ => rfl
  | tag :: tags, cl :: raw, h => by
    simp only [checkRaw, Bool.and_eq_true] at h
    have hc := clause_sound ax oldM ctrs hctrs ts ht M tag cl h.1
    have hr := raw_sound ax oldM ctrs hctrs ts ht M tags raw h.2
    change (clauseTrue _ (cl.map decodeLit) && cnfTrue _ (raw.map (List.map decodeLit))) = true
    rw [Bool.and_eq_true]
    exact ⟨hc, hr⟩
  | [], _ :: _, h => by simp [checkRaw] at h
  | _ :: _, [], h => by simp [checkRaw] at h

def checkAll (oldM : Tags.MT) (ctrs : List Tags.Ctr) (w : List Nat)
    (bounds : List (Nat × Nat)) (ts : List Term) (M : Nat → Option Meaning)
    (cap : Nat) (tags : List Tag) (raw : List (List Nat)) : Bool :=
  ctrs.all (Tags.ctrOK oldM (Tags.centresK w bounds)) &&
  sublist ts (allTerms (Tags.centresK w bounds)) && checkRaw oldM ctrs w ts M cap tags raw

theorem sound (oldM : Tags.MT) (ctrs : List Tags.Ctr) (w : List Nat)
    (bounds : List (Nat × Nat)) (ts : List Term) (M : Nat → Option Meaning)
    (cap : Nat) (tags : List Tag) (raw : List (List Nat))
    (h : checkAll oldM ctrs w bounds ts M cap tags raw = true)
    (S E : Nat → Bool) (ax : AxiomsP S E w (centresOf w bounds) cap) :
    cnfTrue (ParallelShareClauses.assignment (Tags.tau S E oldM ctrs) S ts M)
      (raw.map (List.map decodeLit)) = true := by
  simp only [checkAll, Bool.and_eq_true] at h
  rw [Tags.centresK_eq] at ax
  exact raw_sound ax oldM ctrs h.1.1 ts (sublist_sound h.1.2) M tags raw h.2

theorem refuted_of_check (oldM : Tags.MT) (ctrs : List Tags.Ctr) (w : List Nat)
    (bounds : List (Nat × Nat)) (ts : List Term) (M : Nat → Option Meaning)
    (cap : Nat) (tags : List Tag) (raw : List (List Nat))
    (h : checkAll oldM ctrs w bounds ts M cap tags raw = true)
    (hu : Unsat (raw.map (List.map decodeLit))) : RefutedParallel w bounds cap := by
  intro S E ax
  have hs := sound oldM ctrs w bounds ts M cap tags raw h S E ax
  rw [hu] at hs
  exact Bool.false_ne_true hs

#print axioms sound
#print axioms refuted_of_check
end Snake9.ParallelShareCertificate
