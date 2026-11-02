import Port95M65CountPropagation
namespace Snake9.LocalWindow.CountPropagationPort95
open ForcedShare58 ExtendedShare59 SplitShare62 NeighbourChoice64
set_option maxHeartbeats 0
set_option maxRecDepth 100000

structure Condition where
  corners : List Nat
  lo : Nat
  hi : Nat
deriving DecidableEq

def Condition.Valid (S : Nat → Bool) (c : Condition) : Prop :=
  c.lo≤cnt (fun x => !S x) c.corners ∧ cnt (fun x => !S x) c.corners≤c.hi

def Facts (S : Nat → Bool) (T D : List Nat) : Prop :=
  (∀ v∈T, S v=true) ∧ (∀ v∈D, S v=false)

inductive Step where
  | degree (add : List Nat)
  | select (c : Condition) (add : List Nat)
  | absent (c : Condition) (add : List Nat)

def advance (s : Step) (T D : List Nat) : List Nat × List Nat :=
  match s with
  | .degree add => (T,D++add)
  | .select _ add => (T++add,D)
  | .absent _ add => (T,D++add)

def stepCheck (cs : List Condition) (T D : List Nat) : Step → Bool
  | .degree add => forceCheckPlus T add
  | .select c add => cs.contains c && add.all (fun q =>
      decide (c.hi < cnt (fun x => (q::D).contains x) c.corners))
  | .absent c add => cs.contains c && add.all (fun q =>
      decide (c.corners.length < c.lo+cnt (fun x => (q::T).contains x) c.corners))

theorem step_sound (S : Nat → Bool) (cs : List Condition) (T D : List Nat) (s : Step)
    (hc : ∀ c∈cs, c.Valid S) (hf : Facts S T D)
    (hd : ∀ v, S v=true → cnt S (nbrs v)≤2) (hcheck : stepCheck cs T D s=true) :
    Facts S (advance s T D).1 (advance s T D).2 := by
  rcases hf with ⟨hT,hD⟩
  cases s with
  | degree add =>
    refine ⟨hT,?_⟩
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hD v hv
    · exact forced_absent_plus S T add hT hd hcheck v hv
  | select c add =>
    obtain ⟨hm,ha⟩ := Bool.and_eq_true_iff.mp hcheck
    have hcap := (hc c (List.contains_iff.mp hm)).2
    refine ⟨?_,hD⟩
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hT v hv
    · exact selected_from_upper S D c.corners c.hi v hD hcap
        (of_decide_eq_true (List.all_eq_true.mp ha v hv))
  | absent c add =>
    obtain ⟨hm,ha⟩ := Bool.and_eq_true_iff.mp hcheck
    have hcap := (hc c (List.contains_iff.mp hm)).1
    refine ⟨hT,?_⟩
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hD v hv
    · exact absent_from_lower S T c.corners c.lo v hT hcap
        (of_decide_eq_true (List.all_eq_true.mp ha v hv))

def run (T D : List Nat) : List Step → List Nat × List Nat
  | [] => (T,D)
  | s::ss => run (advance s T D).1 (advance s T D).2 ss

def traceCheck (cs : List Condition) (T D : List Nat) : List Step → Bool
  | [] => true
  | s::ss => stepCheck cs T D s &&
      traceCheck cs (advance s T D).1 (advance s T D).2 ss

theorem trace_sound (S : Nat → Bool) (cs : List Condition) (T D : List Nat)
    (ss : List Step) (hc : ∀ c∈cs, c.Valid S) (hf : Facts S T D)
    (hd : ∀ v, S v=true → cnt S (nbrs v)≤2) (hcheck : traceCheck cs T D ss=true) :
    Facts S (run T D ss).1 (run T D ss).2 := by
  induction ss generalizing T D with
  | nil => exact hf
  | cons s ss ih =>
    obtain ⟨hs,ht⟩ := Bool.and_eq_true_iff.mp hcheck
    exact ih _ _ (step_sound S cs T D s hc hf hd hs) ht

inductive Ending where
  | degree
  | upper (c : Condition)
  | lower (c : Condition)
  | share (mask : Nat)

def endingCheck (cs : List Condition) (C : List Nat) (L : Nat) (T D : List Nat) : Ending → Bool
  | .degree => badCheck T
  | .upper c => cs.contains c && decide (c.hi < cnt (fun x => D.contains x) c.corners)
  | .lower c => cs.contains c && decide (c.corners.length < c.lo+cnt (fun x => T.contains x) c.corners)
  | .share mask => maskCheck mask D && decide (L≤(C.map (shareLocal 12 (allowed mask))).sum)

theorem ending_sound (S : Nat → Bool) (cs : List Condition) (W C T D : List Nat)
    (L : Nat) (e : Ending) (hc : ∀ c∈cs, c.Valid S) (hf : Facts S T D)
    (hW : ∀ v∈W, S v=true) (hd : ∀ v, S v=true → cnt S (nbrs v)≤2)
    (hlt : ∀ v, S v=true → v<512) (hp : supportCheck W C=true)
    (hcheck : endingCheck cs C L T D e=true) : L≤(C.map (shareLocal 12 S)).sum := by
  cases e with
  | degree => exact False.elim (bad_impossible S T hf.1 hd hcheck)
  | upper c =>
    obtain ⟨hm,hb⟩ := Bool.and_eq_true_iff.mp hcheck
    exact False.elim (upper_contradiction S D c.corners c.hi hf.2
      (hc c (List.contains_iff.mp hm)).2 (of_decide_eq_true hb))
  | lower c =>
    obtain ⟨hm,hb⟩ := Bool.and_eq_true_iff.mp hcheck
    exact False.elim (lower_contradiction S T c.corners c.lo hf.1
      (hc c (List.contains_iff.mp hm)).1 (of_decide_eq_true hb))
  | share mask =>
    obtain ⟨hm,hb⟩ := Bool.and_eq_true_iff.mp hcheck
    exact (of_decide_eq_true hb).trans
      (mask_share_of_absent 12 mask S W D C hW hf.2 hlt hp hm)

theorem trace_share (S : Nat → Bool) (cs : List Condition) (W C T D : List Nat)
    (L : Nat) (ss : List Step) (e : Ending)
    (hc : ∀ c∈cs, c.Valid S) (hf : Facts S T D)
    (hW : ∀ v∈W, S v=true) (hd : ∀ v, S v=true → cnt S (nbrs v)≤2)
    (hlt : ∀ v, S v=true → v<512) (hp : supportCheck W C=true)
    (ht : traceCheck cs T D ss=true)
    (he : endingCheck cs C L (run T D ss).1 (run T D ss).2 e=true) :
    L≤(C.map (shareLocal 12 S)).sum :=
  ending_sound S cs W C _ _ L e hc (trace_sound S cs T D ss hc hf hd ht) hW hd hlt hp he

#print axioms step_sound
#print axioms trace_sound
#print axioms ending_sound
#print axioms trace_share
end Snake9.LocalWindow.CountPropagationPort95
