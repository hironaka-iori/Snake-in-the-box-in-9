import Share186.CapData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185

theorem split_layers_perm {α β : Type} (xs : List α) (f g : α → List β) :
    (xs.flatMap (fun x => f x ++ g x)).Perm (xs.flatMap f ++ xs.flatMap g) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    apply (ih.append_left (f x ++ g x)).trans
    simpa only [List.append_assoc] using
      (List.perm_append_comm_assoc (g x) (xs.flatMap f) (xs.flatMap g)).append_left (f x)

theorem threshold_layers_perm (qs : List Nat) :
    ((qs.flatMap (fun q => (List.range 14).map (fun t => (q,t+1)))) ++
      qs.map (fun q => (q,15))).Perm
    (qs.flatMap (fun q => (List.range 15).map (fun t => (q,t+1)))) := by
  have h := (split_layers_perm qs
    (fun q => (List.range 14).map (fun t => (q,t+1)))
    (fun q => [(q,15)])).symm
  have hr (q : Nat) : (List.range 15).map (fun t => (q,t+1)) =
      (List.range 14).map (fun t => (q,t+1)) ++ [(q,15)] := by
    rw [show 15 = 14+1 from rfl,List.range_succ,List.map_append]
    rfl
  simpa only [← List.map_eq_flatMap, ← hr] using h

theorem pair_isPerm_of_perm {xs ys : List (Nat × Nat)} (h : xs.Perm ys) :
    xs.isPerm ys = true := by
  have heq : (instBEqProd : BEq (Nat × Nat)) = instBEqOfDecidableEq := by
    apply congrArg BEq.mk
    funext a b
    exact Bool.beq_eq_decide_eq a b
  rw [heq]
  exact List.isPerm_iff.mpr h

theorem base_of_posU (l : List Nat) (h : l.all (posU meaningDirect smeaningDirect) = true) :
    l.all (baseOKS meaningDirect smeaningDirect) = true := by
  apply List.all_eq_true.mpr
  intro a ha
  have hu := List.all_eq_true.mp h a ha
  simp only [posU,Bool.and_eq_true] at hu
  have hp := posS_parts hu.1
  simp [baseOKS,hp.2.1,hp.2.2,hu.2]

#print axioms split_layers_perm
#print axioms threshold_layers_perm
#print axioms pair_isPerm_of_perm
#print axioms base_of_posU
end Snake9.LocalWindow.ShareWindow185
