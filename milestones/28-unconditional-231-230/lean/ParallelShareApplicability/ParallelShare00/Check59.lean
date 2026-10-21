import ParallelShareApplicability.ParallelShare00.Check59Part0
import ParallelShareApplicability.ParallelShare00.Check59Part1
import ParallelShareApplicability.ParallelShare00.Check59Part2
import ParallelShareApplicability.ParallelShare00.Check59Part3
import ParallelShareApplicability.ParallelShare00.Check59Part4
import ParallelShareApplicability.ParallelShare00.Check59Part5
import ParallelShareApplicability.ParallelShare00.Check59Part6
import ParallelShareApplicability.ParallelShare00.Check59Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts59Refined : List (List Tag × List (List Nat)) := [((tags59.drop 0).take 16, (raw59.drop 0).take 16), ((tags59.drop 16).take 16, (raw59.drop 16).take 16), ((tags59.drop 32).take 16, (raw59.drop 32).take 16), ((tags59.drop 48).take 16, (raw59.drop 48).take 16), ((tags59.drop 64).take 16, (raw59.drop 64).take 16), ((tags59.drop 80).take 16, (raw59.drop 80).take 16), ((tags59.drop 96).take 16, (raw59.drop 96).take 16), ((tags59.drop 112).take 16, (raw59.drop 112).take 16)]

theorem check59 : checkRaw oldMeaning ctrs window terms meaning 20 tags59 raw59 = true := by
  have ht : parts59Refined.flatMap Prod.fst = tags59 := by rfl
  have hr : parts59Refined.flatMap Prod.snd = raw59 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts59Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check59Part0
  · exact check59Part1
  · exact check59Part2
  · exact check59Part3
  · exact check59Part4
  · exact check59Part5
  · exact check59Part6
  · exact check59Part7
end Snake9.LocalWindow.ParallelShare00Applicability
