import Rigidity
import Mathlib.Data.Finset.Card

namespace Snake9.Diversity

theorem same_vertices_same_order_or_reverse {m : Nat} (p q : Snake m)
    (selected : ∀ i, InPath p (q.vertex i)) :
    (∀ i, p.vertex i = q.vertex i) ∨
    (∀ i : Fin (m+1), p.vertex ⟨m-i.val, by omega⟩ = q.vertex i) := by
  obtain ⟨e,hm,h | h⟩ := Contraction.selected_path_contiguous p q selected
  · left
    have last := h ⟨m,by omega⟩
    simp only [Fin.val_mk] at last
    have bound := (e ⟨m,by omega⟩).isLt
    have zero : (e 0).val = 0 := by omega
    intro i
    have eq : e i = i := by
      apply Fin.ext
      have := h i
      omega
    simpa only [eq] using hm i
  · right
    have last := h ⟨m,by omega⟩
    simp only [Fin.val_mk] at last
    have bound := (e 0).isLt
    have zero : (e 0).val = m := by omega
    intro i
    have eq : e i = ⟨m-i.val,by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      have := h i
      omega
    simpa only [eq] using hm i

theorem equal_size_exchange {α : Type*} [DecidableEq α] (s t : Finset α)
    (h : s.card = t.card) : (s \ t).card = (t \ s).card :=
  Finset.card_sdiff_comm h

theorem retreat_exchange {α : Type*} [DecidableEq α] (s t : Finset α)
    (h : t.card + 1 = s.card) : (t \ s).card + 1 = (s \ t).card := by
  have hs := Finset.card_sdiff_add_card_inter s t
  have ht := Finset.card_sdiff_add_card_inter t s
  rw [Finset.inter_comm t s] at ht
  omega

#print axioms same_vertices_same_order_or_reverse
#print axioms equal_size_exchange
#print axioms retreat_exchange
end Snake9.Diversity
