import ParallelShareApplicability.ParallelShare00.Check50Part0
import ParallelShareApplicability.ParallelShare00.Check50Part1
import ParallelShareApplicability.ParallelShare00.Check50Part2
import ParallelShareApplicability.ParallelShare00.Check50Part3
import ParallelShareApplicability.ParallelShare00.Check50Part4
import ParallelShareApplicability.ParallelShare00.Check50Part5
import ParallelShareApplicability.ParallelShare00.Check50Part6
import ParallelShareApplicability.ParallelShare00.Check50Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts50Refined : List (List Tag × List (List Nat)) := [((tags50.drop 0).take 16, (raw50.drop 0).take 16), ((tags50.drop 16).take 16, (raw50.drop 16).take 16), ((tags50.drop 32).take 16, (raw50.drop 32).take 16), ((tags50.drop 48).take 16, (raw50.drop 48).take 16), ((tags50.drop 64).take 16, (raw50.drop 64).take 16), ((tags50.drop 80).take 16, (raw50.drop 80).take 16), ((tags50.drop 96).take 16, (raw50.drop 96).take 16), ((tags50.drop 112).take 16, (raw50.drop 112).take 16)]

theorem check50 : checkRaw oldMeaning ctrs window terms meaning 20 tags50 raw50 = true := by
  have ht : parts50Refined.flatMap Prod.fst = tags50 := by rfl
  have hr : parts50Refined.flatMap Prod.snd = raw50 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts50Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check50Part0
  · exact check50Part1
  · exact check50Part2
  · exact check50Part3
  · exact check50Part4
  · exact check50Part5
  · exact check50Part6
  · exact check50Part7
end Snake9.LocalWindow.ParallelShare00Applicability
