import ParallelShareApplicability.ParallelShare00.Check49Part0
import ParallelShareApplicability.ParallelShare00.Check49Part1
import ParallelShareApplicability.ParallelShare00.Check49Part2
import ParallelShareApplicability.ParallelShare00.Check49Part3
import ParallelShareApplicability.ParallelShare00.Check49Part4
import ParallelShareApplicability.ParallelShare00.Check49Part5
import ParallelShareApplicability.ParallelShare00.Check49Part6
import ParallelShareApplicability.ParallelShare00.Check49Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts49Refined : List (List Tag × List (List Nat)) := [((tags49.drop 0).take 16, (raw49.drop 0).take 16), ((tags49.drop 16).take 16, (raw49.drop 16).take 16), ((tags49.drop 32).take 16, (raw49.drop 32).take 16), ((tags49.drop 48).take 16, (raw49.drop 48).take 16), ((tags49.drop 64).take 16, (raw49.drop 64).take 16), ((tags49.drop 80).take 16, (raw49.drop 80).take 16), ((tags49.drop 96).take 16, (raw49.drop 96).take 16), ((tags49.drop 112).take 16, (raw49.drop 112).take 16)]

theorem check49 : checkRaw oldMeaning ctrs window terms meaning 20 tags49 raw49 = true := by
  have ht : parts49Refined.flatMap Prod.fst = tags49 := by rfl
  have hr : parts49Refined.flatMap Prod.snd = raw49 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts49Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check49Part0
  · exact check49Part1
  · exact check49Part2
  · exact check49Part3
  · exact check49Part4
  · exact check49Part5
  · exact check49Part6
  · exact check49Part7
end Snake9.LocalWindow.ParallelShare00Applicability
