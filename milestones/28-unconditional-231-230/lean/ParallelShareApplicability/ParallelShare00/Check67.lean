import ParallelShareApplicability.ParallelShare00.Check67Part0
import ParallelShareApplicability.ParallelShare00.Check67Part1
import ParallelShareApplicability.ParallelShare00.Check67Part2
import ParallelShareApplicability.ParallelShare00.Check67Part3
import ParallelShareApplicability.ParallelShare00.Check67Part4
import ParallelShareApplicability.ParallelShare00.Check67Part5
import ParallelShareApplicability.ParallelShare00.Check67Part6
import ParallelShareApplicability.ParallelShare00.Check67Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts67Refined : List (List Tag × List (List Nat)) := [((tags67.drop 0).take 16, (raw67.drop 0).take 16), ((tags67.drop 16).take 16, (raw67.drop 16).take 16), ((tags67.drop 32).take 16, (raw67.drop 32).take 16), ((tags67.drop 48).take 16, (raw67.drop 48).take 16), ((tags67.drop 64).take 16, (raw67.drop 64).take 16), ((tags67.drop 80).take 16, (raw67.drop 80).take 16), ((tags67.drop 96).take 16, (raw67.drop 96).take 16), ((tags67.drop 112).take 16, (raw67.drop 112).take 16)]

theorem check67 : checkRaw oldMeaning ctrs window terms meaning 20 tags67 raw67 = true := by
  have ht : parts67Refined.flatMap Prod.fst = tags67 := by rfl
  have hr : parts67Refined.flatMap Prod.snd = raw67 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts67Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check67Part0
  · exact check67Part1
  · exact check67Part2
  · exact check67Part3
  · exact check67Part4
  · exact check67Part5
  · exact check67Part6
  · exact check67Part7
end Snake9.LocalWindow.ParallelShare00Applicability
