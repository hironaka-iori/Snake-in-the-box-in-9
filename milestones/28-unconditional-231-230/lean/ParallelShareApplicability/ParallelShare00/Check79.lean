import ParallelShareApplicability.ParallelShare00.Check79Part0
import ParallelShareApplicability.ParallelShare00.Check79Part1
import ParallelShareApplicability.ParallelShare00.Check79Part2
import ParallelShareApplicability.ParallelShare00.Check79Part3
import ParallelShareApplicability.ParallelShare00.Check79Part4
import ParallelShareApplicability.ParallelShare00.Check79Part5
import ParallelShareApplicability.ParallelShare00.Check79Part6
import ParallelShareApplicability.ParallelShare00.Check79Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts79Refined : List (List Tag × List (List Nat)) := [((tags79.drop 0).take 16, (raw79.drop 0).take 16), ((tags79.drop 16).take 16, (raw79.drop 16).take 16), ((tags79.drop 32).take 16, (raw79.drop 32).take 16), ((tags79.drop 48).take 16, (raw79.drop 48).take 16), ((tags79.drop 64).take 16, (raw79.drop 64).take 16), ((tags79.drop 80).take 16, (raw79.drop 80).take 16), ((tags79.drop 96).take 16, (raw79.drop 96).take 16), ((tags79.drop 112).take 16, (raw79.drop 112).take 16)]

theorem check79 : checkRaw oldMeaning ctrs window terms meaning 20 tags79 raw79 = true := by
  have ht : parts79Refined.flatMap Prod.fst = tags79 := by rfl
  have hr : parts79Refined.flatMap Prod.snd = raw79 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts79Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check79Part0
  · exact check79Part1
  · exact check79Part2
  · exact check79Part3
  · exact check79Part4
  · exact check79Part5
  · exact check79Part6
  · exact check79Part7
end Snake9.LocalWindow.ParallelShare00Applicability
