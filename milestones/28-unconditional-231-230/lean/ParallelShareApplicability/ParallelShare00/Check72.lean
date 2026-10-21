import ParallelShareApplicability.ParallelShare00.Check72Part0
import ParallelShareApplicability.ParallelShare00.Check72Part1
import ParallelShareApplicability.ParallelShare00.Check72Part2
import ParallelShareApplicability.ParallelShare00.Check72Part3
import ParallelShareApplicability.ParallelShare00.Check72Part4
import ParallelShareApplicability.ParallelShare00.Check72Part5
import ParallelShareApplicability.ParallelShare00.Check72Part6
import ParallelShareApplicability.ParallelShare00.Check72Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts72Refined : List (List Tag × List (List Nat)) := [((tags72.drop 0).take 16, (raw72.drop 0).take 16), ((tags72.drop 16).take 16, (raw72.drop 16).take 16), ((tags72.drop 32).take 16, (raw72.drop 32).take 16), ((tags72.drop 48).take 16, (raw72.drop 48).take 16), ((tags72.drop 64).take 16, (raw72.drop 64).take 16), ((tags72.drop 80).take 16, (raw72.drop 80).take 16), ((tags72.drop 96).take 16, (raw72.drop 96).take 16), ((tags72.drop 112).take 16, (raw72.drop 112).take 16)]

theorem check72 : checkRaw oldMeaning ctrs window terms meaning 20 tags72 raw72 = true := by
  have ht : parts72Refined.flatMap Prod.fst = tags72 := by rfl
  have hr : parts72Refined.flatMap Prod.snd = raw72 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts72Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check72Part0
  · exact check72Part1
  · exact check72Part2
  · exact check72Part3
  · exact check72Part4
  · exact check72Part5
  · exact check72Part6
  · exact check72Part7
end Snake9.LocalWindow.ParallelShare00Applicability
