namespace LossOneSignature178
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem loss_one_corner_signature : ∀ d : Fin 10, ∀ e : Fin 37,
    0<d.val → e.val≤(9-d.val)*(8-d.val)/2 →
    (12*e.val)%d.val=1 → d.val=5 ∧ e.val=3 := by decide

#print axioms loss_one_corner_signature
end LossOneSignature178
