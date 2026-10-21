import ParallelShareApplicability.ParallelShare00.Check77Part0
import ParallelShareApplicability.ParallelShare00.Check77Part1
import ParallelShareApplicability.ParallelShare00.Check77Part2
import ParallelShareApplicability.ParallelShare00.Check77Part3
import ParallelShareApplicability.ParallelShare00.Check77Part4
import ParallelShareApplicability.ParallelShare00.Check77Part5
import ParallelShareApplicability.ParallelShare00.Check77Part6
import ParallelShareApplicability.ParallelShare00.Check77Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts77Refined : List (List Tag × List (List Nat)) := [((tags77.drop 0).take 16, (raw77.drop 0).take 16), ((tags77.drop 16).take 16, (raw77.drop 16).take 16), ((tags77.drop 32).take 16, (raw77.drop 32).take 16), ((tags77.drop 48).take 16, (raw77.drop 48).take 16), ((tags77.drop 64).take 16, (raw77.drop 64).take 16), ((tags77.drop 80).take 16, (raw77.drop 80).take 16), ((tags77.drop 96).take 16, (raw77.drop 96).take 16), ((tags77.drop 112).take 16, (raw77.drop 112).take 16)]

theorem check77 : checkRaw oldMeaning ctrs window terms meaning 20 tags77 raw77 = true := by
  have ht : parts77Refined.flatMap Prod.fst = tags77 := by rfl
  have hr : parts77Refined.flatMap Prod.snd = raw77 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts77Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check77Part0
  · exact check77Part1
  · exact check77Part2
  · exact check77Part3
  · exact check77Part4
  · exact check77Part5
  · exact check77Part6
  · exact check77Part7
end Snake9.LocalWindow.ParallelShare00Applicability
