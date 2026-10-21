import ParallelShareApplicability.ParallelShare00.Check54Part0
import ParallelShareApplicability.ParallelShare00.Check54Part1
import ParallelShareApplicability.ParallelShare00.Check54Part2
import ParallelShareApplicability.ParallelShare00.Check54Part3
import ParallelShareApplicability.ParallelShare00.Check54Part4
import ParallelShareApplicability.ParallelShare00.Check54Part5
import ParallelShareApplicability.ParallelShare00.Check54Part6
import ParallelShareApplicability.ParallelShare00.Check54Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts54Refined : List (List Tag × List (List Nat)) := [((tags54.drop 0).take 16, (raw54.drop 0).take 16), ((tags54.drop 16).take 16, (raw54.drop 16).take 16), ((tags54.drop 32).take 16, (raw54.drop 32).take 16), ((tags54.drop 48).take 16, (raw54.drop 48).take 16), ((tags54.drop 64).take 16, (raw54.drop 64).take 16), ((tags54.drop 80).take 16, (raw54.drop 80).take 16), ((tags54.drop 96).take 16, (raw54.drop 96).take 16), ((tags54.drop 112).take 16, (raw54.drop 112).take 16)]

theorem check54 : checkRaw oldMeaning ctrs window terms meaning 20 tags54 raw54 = true := by
  have ht : parts54Refined.flatMap Prod.fst = tags54 := by rfl
  have hr : parts54Refined.flatMap Prod.snd = raw54 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts54Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check54Part0
  · exact check54Part1
  · exact check54Part2
  · exact check54Part3
  · exact check54Part4
  · exact check54Part5
  · exact check54Part6
  · exact check54Part7
end Snake9.LocalWindow.ParallelShare00Applicability
