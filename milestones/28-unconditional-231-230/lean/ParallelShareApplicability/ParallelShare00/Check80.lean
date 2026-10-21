import ParallelShareApplicability.ParallelShare00.Check80Part0
import ParallelShareApplicability.ParallelShare00.Check80Part1
import ParallelShareApplicability.ParallelShare00.Check80Part2
import ParallelShareApplicability.ParallelShare00.Check80Part3
import ParallelShareApplicability.ParallelShare00.Check80Part4
import ParallelShareApplicability.ParallelShare00.Check80Part5
import ParallelShareApplicability.ParallelShare00.Check80Part6
import ParallelShareApplicability.ParallelShare00.Check80Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts80Refined : List (List Tag × List (List Nat)) := [((tags80.drop 0).take 16, (raw80.drop 0).take 16), ((tags80.drop 16).take 16, (raw80.drop 16).take 16), ((tags80.drop 32).take 16, (raw80.drop 32).take 16), ((tags80.drop 48).take 16, (raw80.drop 48).take 16), ((tags80.drop 64).take 16, (raw80.drop 64).take 16), ((tags80.drop 80).take 16, (raw80.drop 80).take 16), ((tags80.drop 96).take 16, (raw80.drop 96).take 16), ((tags80.drop 112).take 16, (raw80.drop 112).take 16)]

theorem check80 : checkRaw oldMeaning ctrs window terms meaning 20 tags80 raw80 = true := by
  have ht : parts80Refined.flatMap Prod.fst = tags80 := by rfl
  have hr : parts80Refined.flatMap Prod.snd = raw80 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts80Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check80Part0
  · exact check80Part1
  · exact check80Part2
  · exact check80Part3
  · exact check80Part4
  · exact check80Part5
  · exact check80Part6
  · exact check80Part7
end Snake9.LocalWindow.ParallelShare00Applicability
