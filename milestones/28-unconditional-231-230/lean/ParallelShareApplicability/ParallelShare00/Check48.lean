import ParallelShareApplicability.ParallelShare00.Check48Part0
import ParallelShareApplicability.ParallelShare00.Check48Part1
import ParallelShareApplicability.ParallelShare00.Check48Part2
import ParallelShareApplicability.ParallelShare00.Check48Part3
import ParallelShareApplicability.ParallelShare00.Check48Part4
import ParallelShareApplicability.ParallelShare00.Check48Part5
import ParallelShareApplicability.ParallelShare00.Check48Part6
import ParallelShareApplicability.ParallelShare00.Check48Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts48Refined : List (List Tag × List (List Nat)) := [((tags48.drop 0).take 16, (raw48.drop 0).take 16), ((tags48.drop 16).take 16, (raw48.drop 16).take 16), ((tags48.drop 32).take 16, (raw48.drop 32).take 16), ((tags48.drop 48).take 16, (raw48.drop 48).take 16), ((tags48.drop 64).take 16, (raw48.drop 64).take 16), ((tags48.drop 80).take 16, (raw48.drop 80).take 16), ((tags48.drop 96).take 16, (raw48.drop 96).take 16), ((tags48.drop 112).take 16, (raw48.drop 112).take 16)]

theorem check48 : checkRaw oldMeaning ctrs window terms meaning 20 tags48 raw48 = true := by
  have ht : parts48Refined.flatMap Prod.fst = tags48 := by rfl
  have hr : parts48Refined.flatMap Prod.snd = raw48 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts48Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check48Part0
  · exact check48Part1
  · exact check48Part2
  · exact check48Part3
  · exact check48Part4
  · exact check48Part5
  · exact check48Part6
  · exact check48Part7
end Snake9.LocalWindow.ParallelShare00Applicability
