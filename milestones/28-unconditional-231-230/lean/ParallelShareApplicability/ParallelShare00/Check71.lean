import ParallelShareApplicability.ParallelShare00.Check71Part0
import ParallelShareApplicability.ParallelShare00.Check71Part1
import ParallelShareApplicability.ParallelShare00.Check71Part2
import ParallelShareApplicability.ParallelShare00.Check71Part3
import ParallelShareApplicability.ParallelShare00.Check71Part4
import ParallelShareApplicability.ParallelShare00.Check71Part5
import ParallelShareApplicability.ParallelShare00.Check71Part6
import ParallelShareApplicability.ParallelShare00.Check71Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts71Refined : List (List Tag × List (List Nat)) := [((tags71.drop 0).take 16, (raw71.drop 0).take 16), ((tags71.drop 16).take 16, (raw71.drop 16).take 16), ((tags71.drop 32).take 16, (raw71.drop 32).take 16), ((tags71.drop 48).take 16, (raw71.drop 48).take 16), ((tags71.drop 64).take 16, (raw71.drop 64).take 16), ((tags71.drop 80).take 16, (raw71.drop 80).take 16), ((tags71.drop 96).take 16, (raw71.drop 96).take 16), ((tags71.drop 112).take 16, (raw71.drop 112).take 16)]

theorem check71 : checkRaw oldMeaning ctrs window terms meaning 20 tags71 raw71 = true := by
  have ht : parts71Refined.flatMap Prod.fst = tags71 := by rfl
  have hr : parts71Refined.flatMap Prod.snd = raw71 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts71Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check71Part0
  · exact check71Part1
  · exact check71Part2
  · exact check71Part3
  · exact check71Part4
  · exact check71Part5
  · exact check71Part6
  · exact check71Part7
end Snake9.LocalWindow.ParallelShare00Applicability
