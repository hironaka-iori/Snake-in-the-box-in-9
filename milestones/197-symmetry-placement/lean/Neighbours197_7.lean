import NormalForm197
namespace NormalForm197
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem neighbours7 : ∀ i : Fin 16, ∀ j : Fin 8,
  let y := 112 + i.val
  label (Nat.xor (embed y) (2^j.val)) =
    if j.val = 1 then matching y
    else Nat.xor y (2^(if j.val < 1 then j.val else j.val - 1)) := by decide +kernel

#print axioms neighbours7
end NormalForm197
