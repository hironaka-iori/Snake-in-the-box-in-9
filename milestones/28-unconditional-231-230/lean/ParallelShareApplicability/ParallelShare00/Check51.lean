import ParallelShareApplicability.ParallelShare00.Check51Part0
import ParallelShareApplicability.ParallelShare00.Check51Part1
import ParallelShareApplicability.ParallelShare00.Check51Part2
import ParallelShareApplicability.ParallelShare00.Check51Part3
import ParallelShareApplicability.ParallelShare00.Check51Part4
import ParallelShareApplicability.ParallelShare00.Check51Part5
import ParallelShareApplicability.ParallelShare00.Check51Part6
import ParallelShareApplicability.ParallelShare00.Check51Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts51Refined : List (List Tag × List (List Nat)) := [((tags51.drop 0).take 16, (raw51.drop 0).take 16), ((tags51.drop 16).take 16, (raw51.drop 16).take 16), ((tags51.drop 32).take 16, (raw51.drop 32).take 16), ((tags51.drop 48).take 16, (raw51.drop 48).take 16), ((tags51.drop 64).take 16, (raw51.drop 64).take 16), ((tags51.drop 80).take 16, (raw51.drop 80).take 16), ((tags51.drop 96).take 16, (raw51.drop 96).take 16), ((tags51.drop 112).take 16, (raw51.drop 112).take 16)]

theorem check51 : checkRaw oldMeaning ctrs window terms meaning 20 tags51 raw51 = true := by
  have ht : parts51Refined.flatMap Prod.fst = tags51 := by rfl
  have hr : parts51Refined.flatMap Prod.snd = raw51 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts51Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check51Part0
  · exact check51Part1
  · exact check51Part2
  · exact check51Part3
  · exact check51Part4
  · exact check51Part5
  · exact check51Part6
  · exact check51Part7
end Snake9.LocalWindow.ParallelShare00Applicability
