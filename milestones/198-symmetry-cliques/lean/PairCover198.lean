import PairData198
namespace PairCover198

theorem cover {P : Fin 12 → Prop}
 (h : ∀ b : Fin 4, ∀ i : Fin 3, P ⟨3*b.val+i.val,by omega⟩)
 (v : Fin 12) : P v := by
 have he : 3*(v.val/3)+v.val%3=v.val := by omega
 have hv := h ⟨v.val/3,by omega⟩ ⟨v.val%3,by omega⟩
 simpa only [Fin.val_mk,he] using hv

#print axioms cover
end PairCover198
