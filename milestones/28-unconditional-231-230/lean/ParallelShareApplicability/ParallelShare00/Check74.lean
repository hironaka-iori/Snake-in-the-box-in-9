import ParallelShareApplicability.ParallelShare00.Check74Part0
import ParallelShareApplicability.ParallelShare00.Check74Part1
import ParallelShareApplicability.ParallelShare00.Check74Part2
import ParallelShareApplicability.ParallelShare00.Check74Part3
import ParallelShareApplicability.ParallelShare00.Check74Part4
import ParallelShareApplicability.ParallelShare00.Check74Part5
import ParallelShareApplicability.ParallelShare00.Check74Part6
import ParallelShareApplicability.ParallelShare00.Check74Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts74Refined : List (List Tag × List (List Nat)) := [((tags74.drop 0).take 16, (raw74.drop 0).take 16), ((tags74.drop 16).take 16, (raw74.drop 16).take 16), ((tags74.drop 32).take 16, (raw74.drop 32).take 16), ((tags74.drop 48).take 16, (raw74.drop 48).take 16), ((tags74.drop 64).take 16, (raw74.drop 64).take 16), ((tags74.drop 80).take 16, (raw74.drop 80).take 16), ((tags74.drop 96).take 16, (raw74.drop 96).take 16), ((tags74.drop 112).take 16, (raw74.drop 112).take 16)]

theorem check74 : checkRaw oldMeaning ctrs window terms meaning 20 tags74 raw74 = true := by
  have ht : parts74Refined.flatMap Prod.fst = tags74 := by rfl
  have hr : parts74Refined.flatMap Prod.snd = raw74 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts74Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check74Part0
  · exact check74Part1
  · exact check74Part2
  · exact check74Part3
  · exact check74Part4
  · exact check74Part5
  · exact check74Part6
  · exact check74Part7
end Snake9.LocalWindow.ParallelShare00Applicability
