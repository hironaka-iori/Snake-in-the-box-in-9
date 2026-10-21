import ParallelShareApplicability.ParallelShare00.Check85Part0
import ParallelShareApplicability.ParallelShare00.Check85Part1
import ParallelShareApplicability.ParallelShare00.Check85Part2
import ParallelShareApplicability.ParallelShare00.Check85Part3
import ParallelShareApplicability.ParallelShare00.Check85Part4
import ParallelShareApplicability.ParallelShare00.Check85Part5
import ParallelShareApplicability.ParallelShare00.Check85Part6
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts85Refined : List (List Tag × List (List Nat)) := [((tags85.drop 0).take 16, (raw85.drop 0).take 16), ((tags85.drop 16).take 16, (raw85.drop 16).take 16), ((tags85.drop 32).take 16, (raw85.drop 32).take 16), ((tags85.drop 48).take 16, (raw85.drop 48).take 16), ((tags85.drop 64).take 16, (raw85.drop 64).take 16), ((tags85.drop 80).take 16, (raw85.drop 80).take 16), ((tags85.drop 96).take 16, (raw85.drop 96).take 16)]

theorem check85 : checkRaw oldMeaning ctrs window terms meaning 20 tags85 raw85 = true := by
  have ht : parts85Refined.flatMap Prod.fst = tags85 := by rfl
  have hr : parts85Refined.flatMap Prod.snd = raw85 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts85Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check85Part0
  · exact check85Part1
  · exact check85Part2
  · exact check85Part3
  · exact check85Part4
  · exact check85Part5
  · exact check85Part6
end Snake9.LocalWindow.ParallelShare00Applicability
