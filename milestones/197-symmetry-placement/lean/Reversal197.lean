import LayerJoining
namespace Reversal197
open LayerJoining

theorem reversalObstruction {V : Type} {R : V → V → Prop} {m : Nat}
    (p : InducedPath V R m) (g : V → V)
    (noFixed : ∀ v, g v ≠ v)
    (noPartnerEdge : ∀ v, ¬ R v (g v))
    (reverse : ∀ i : Fin (m+1),
      g (p.vertex i) = p.vertex ⟨m-i.val, by omega⟩) : False := by
  let i : Fin (m+1) := ⟨m/2, by omega⟩
  let j : Fin (m+1) := ⟨m-m/2, by omega⟩
  have hg : g (p.vertex i) = p.vertex j := reverse i
  by_cases he : m % 2 = 0
  · have equal : i = j := by apply Fin.ext; simp only [i,j,Fin.val_mk]; omega
    exact noFixed (p.vertex i) (by simpa only [equal] using hg)
  · have lt : i.val < j.val := by simp only [i,j,Fin.val_mk]; omega
    have edge : R (p.vertex i) (p.vertex j) :=
      (p.induced i j lt).mpr (by simp only [i,j,Fin.val_mk]; omega)
    exact noPartnerEdge (p.vertex i) (by simpa only [hg] using edge)

#print axioms reversalObstruction
end Reversal197
