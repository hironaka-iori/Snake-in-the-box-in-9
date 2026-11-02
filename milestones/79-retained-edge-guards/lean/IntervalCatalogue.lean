import IntervalGuards
import CycleExclusion7202
import CycleExclusion7203
import CycleExclusion7206
import CycleExclusion7211
import CycleExclusion7212
import CycleExclusion7215
import CycleExclusion7216
import CycleExclusion7217
import CycleExclusion7218
import CycleExclusion7219

namespace Snake9.Guards79
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.GraphWalk78
set_option maxHeartbeats 2000000

def intervalKeys72 : List (List Nat × List (Nat × Nat)) := [
([0, 1, 2, 0, 3],[(0,2),(0,4),(0,5),(0,5)]),
([0, 1, 2, 0, 3],[(0,2),(0,5),(0,5),(0,4)]),
([0, 1, 2, 0, 3],[(0,3),(0,5),(0,3),(0,5)]),
([0, 1, 2, 0, 3],[(0,4),(0,5),(0,2),(0,5)]),
([0, 1, 2, 0, 3],[(0,4),(0,5),(0,3),(0,2)]),
([0, 1, 2, 0, 3],[(0,4),(0,5),(0,5),(0,1)]),
([0, 1, 2, 0, 3],[(0,5),(0,5),(0,2),(0,3)]),
([0, 1, 2, 3, 0],[(0,1),(0,5),(0,5),(0,1)]),
([0, 1, 2, 3, 0],[(0,1),(0,21),(0,21),(0,1)]),
([0, 1, 2, 3, 0],[(0,1),(0,21),(0,21),(0,2)])
]

theorem interval_catalogue : ∀ key ∈ intervalKeys72,
    key.2.length = 4 ∧
    (∀ i, i < key.2.length → (key.2.getD i (0,21)).1 ≤ 6 ∧
      ((key.2.getD i (0,21)).2 < 6 ∨ (key.2.getD i (0,21)).2 = 21)) ∧
    Refuted (winOf key.1) key.2 := by
  intro key hk
  simp only [intervalKeys72, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      change i < 4 at hi
      interval_cases i <;> decide
    · exact CycleWindow7202.refuted
  · refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      change i < 4 at hi
      interval_cases i <;> decide
    · exact CycleWindow7203.refuted
  · refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      change i < 4 at hi
      interval_cases i <;> decide
    · exact CycleWindow7206.refuted
  · refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      change i < 4 at hi
      interval_cases i <;> decide
    · exact CycleWindow7211.refuted
  · refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      change i < 4 at hi
      interval_cases i <;> decide
    · exact CycleWindow7212.refuted
  · refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      change i < 4 at hi
      interval_cases i <;> decide
    · exact CycleWindow7215.refuted
  · refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      change i < 4 at hi
      interval_cases i <;> decide
    · exact CycleWindow7216.refuted
  · refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      change i < 4 at hi
      interval_cases i <;> decide
    · exact CycleWindow7217.refuted
  · refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      change i < 4 at hi
      interval_cases i <;> decide
    · exact CycleWindow7218.refuted
  · refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      change i < 4 at hi
      interval_cases i <;> decide
    · exact CycleWindow7219.refuted

theorem interval_forward_retention {m : Nat} (p : Snake m) (r s : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 2) :
    ∀ key ∈ intervalKeys72,
      canon (((canon (dsOf p r 9)).drop (s+2)).take 5) = key.1 →
      ¬ intervalHit (sixCode p r) s 4 false key.2 := by
  intro key hk hshape hhit
  obtain ⟨hlen,hends,href⟩ := interval_catalogue key hk
  exact encoded_interval_forward_exclusion p r s 4 hr (by omega) (by omega)
    key.1 key.2 hlen hends href hshape hhit

theorem interval_reverse_retention {m : Nat} (p : Snake m) (r s : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 2) :
    ∀ key ∈ intervalKeys72,
      canon ((((canon (dsOf p r 9)).drop (s+2)).take 5).reverse) = key.1 →
      ¬ intervalHit (sixCode p r) s 4 true key.2 := by
  intro key hk hshape hhit
  obtain ⟨hlen,hends,href⟩ := interval_catalogue key hk
  exact encoded_interval_reverse_exclusion p r s 4 hr (by omega) (by omega)
    key.1 key.2 hlen hends href hshape hhit

#print axioms interval_catalogue
#print axioms interval_forward_retention
#print axioms interval_reverse_retention
end Snake9.Guards79
