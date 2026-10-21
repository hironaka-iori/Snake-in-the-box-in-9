import ParallelShareApplicability.ParallelShare00.Check45Part0
import ParallelShareApplicability.ParallelShare00.Check45Part1
import ParallelShareApplicability.ParallelShare00.Check45Part2
import ParallelShareApplicability.ParallelShare00.Check45Part3
import ParallelShareApplicability.ParallelShare00.Check45Part4
import ParallelShareApplicability.ParallelShare00.Check45Part5
import ParallelShareApplicability.ParallelShare00.Check45Part6
import ParallelShareApplicability.ParallelShare00.Check45Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts45Refined : List (List Tag × List (List Nat)) := [((tags45.drop 0).take 16, (raw45.drop 0).take 16), ((tags45.drop 16).take 16, (raw45.drop 16).take 16), ((tags45.drop 32).take 16, (raw45.drop 32).take 16), ((tags45.drop 48).take 16, (raw45.drop 48).take 16), ((tags45.drop 64).take 16, (raw45.drop 64).take 16), ((tags45.drop 80).take 16, (raw45.drop 80).take 16), ((tags45.drop 96).take 16, (raw45.drop 96).take 16), ((tags45.drop 112).take 16, (raw45.drop 112).take 16)]

theorem check45 : checkRaw oldMeaning ctrs window terms meaning 20 tags45 raw45 = true := by
  have ht : parts45Refined.flatMap Prod.fst = tags45 := by rfl
  have hr : parts45Refined.flatMap Prod.snd = raw45 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts45Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check45Part0
  · exact check45Part1
  · exact check45Part2
  · exact check45Part3
  · exact check45Part4
  · exact check45Part5
  · exact check45Part6
  · exact check45Part7
end Snake9.LocalWindow.ParallelShare00Applicability
