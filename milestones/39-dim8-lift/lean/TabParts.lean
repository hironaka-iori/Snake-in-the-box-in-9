import TabDefs

namespace Dim8Lift.Tab
theorem all_parts {α : Type} (P : α → Bool) (l : List α)
    (h0 : (l.take 500).all P = true) (h1 : ((l.drop 500).take 500).all P = true)
    (h2 : ((l.drop 1000).take 500).all P = true) (h3 : (l.drop 1500).all P = true) : l.all P = true := by
  rw [← List.take_append_drop 500 l, List.all_append, h0, Bool.true_and]
  rw [← List.take_append_drop 500 (l.drop 500), List.all_append, h1, Bool.true_and, List.drop_drop]
  rw [← List.take_append_drop 500 (l.drop (500 + 500)), List.all_append, List.drop_drop]
  simp only [show 500 + 500 = 1000 from rfl, show 1000 + 500 = 1500 from rfl, h2, h3, Bool.and_self]
end Dim8Lift.Tab
