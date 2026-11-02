import HistoryUnique
import PositionTransfer
import TerminalCount
import CountPhase04
import CountPhase29

namespace Snake9.History84
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78 Snake9.CountGeometry78
open Snake9.ShortRules81 Snake9.LocalWindow.CountPropagation65
set_option maxHeartbeats 2000000

def emits {m : Nat} (p : Snake m) (r : Nat) (sig : List Nat) : Prop :=
  sig <:+ Snake9.History75.prefixes.getD (actualHistory p r) [] ++ [directionId p r]

theorem history0_count {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m)
    (he : emits p r signature0) : 3 ≤ coreAlpha p (r+8) := by
  obtain ⟨hr2,hw⟩ := emitted_unique_word p r signature0 word0 hr (by decide) realization_table_0 he
  obtain ⟨P,hP⟩ := canonical_permutation p (r-2) 11 (by omega)
  have h := TerminalCount.in_snake p P (r-2) (by omega) (by
    intro j hj
    have hj11 : j < 11 := by simpa [TerminalCount.dirs] using hj
    have hp := hP j hj11
    rw [hw] at hp
    exact hp)
  have hi : r-2+10 = r+8 := by omega
  simpa only [hi] using h

theorem history1_count {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m)
    (he : emits p r signature1) : 3 ≤ coreAlpha p (r+6) := by
  obtain ⟨hr2,hw⟩ := emitted_unique_word p r signature1 word1 hr (by decide) realization_table_1 he
  obtain ⟨P,hP⟩ := canonical_permutation p (r-2) 11 (by omega)
  have h := CountPhase04.in_snake p P (r-2) (by omega) (by
    intro j hj
    have hj11 : j < 11 := by simpa [CountPhase04.dirs] using hj
    have hp := hP j hj11
    rw [hw] at hp
    exact hp)
  have hi : r-2+8 = r+6 := by omega
  simpa only [hi] using h

theorem history2_count {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m)
    (he : emits p r signature2) : 3 ≤ coreAlpha p (r+8) := by
  obtain ⟨hr2,hw⟩ := emitted_unique_word p r signature2 word2 hr (by decide) realization_table_2 he
  obtain ⟨P,hP⟩ := canonical_permutation p (r-2) 11 (by omega)
  have h := CountPhase29.in_snake p P (r-2) (by omega) (by
    intro j hj
    have hj11 : j < 11 := by simpa [CountPhase29.dirs] using hj
    have hp := hP j hj11
    rw [hw] at hp
    exact hp)
  have hi : r-2+10 = r+8 := by omega
  simpa only [hi] using h

def historyRules : List (List Nat × Nat) := [(signature0,5),(signature1,3),(signature2,5)]

theorem all_history_exclusions_retained {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) : ∀ rule ∈ historyRules,
      emits p r rule.1 → 2 < digit (sixCode p r) rule.2 := by
  intro rule h he
  simp only [historyRules,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl
  · have hc := history0_count p r hr he
    rw [actual_digit p r 5 hr (by omega)]
    unfold truncatedCount
    simp only [Nat.add_assoc,Nat.reduceAdd]
    omega
  · have hc := history1_count p r hr he
    rw [actual_digit p r 3 hr (by omega)]
    unfold truncatedCount
    simp only [Nat.add_assoc,Nat.reduceAdd]
    omega
  · have hc := history2_count p r hr he
    rw [actual_digit p r 5 hr (by omega)]
    unfold truncatedCount
    simp only [Nat.add_assoc,Nat.reduceAdd]
    omega

def builderHistoryHit (q di code : Nat) (rule : List Nat × Nat) : Prop :=
  let hist := Snake9.History75.prefixes.getD q [] ++ [di]
  3 ≤ hist.length ∧ hist.drop (hist.length-3) = rule.1 ∧ digit code rule.2 ≤ 2

theorem actual_builder_history_retained {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) : ∀ rule ∈ historyRules,
      ¬ builderHistoryHit (actualHistory p r) (directionId p r) (sixCode p r) rule := by
  intro rule h hh
  have he : emits p r rule.1 := by
    unfold emits
    rw [← hh.2.1]
    exact List.drop_suffix _ _
  have hc := all_history_exclusions_retained p r hr rule h he
  exact (Nat.not_le_of_gt hc) hh.2.2

#print axioms history0_count
#print axioms history1_count
#print axioms history2_count
#print axioms all_history_exclusions_retained
#print axioms actual_builder_history_retained
end Snake9.History84
