import ParallelShareApplicability.ParallelShare00.Check81Part0
import ParallelShareApplicability.ParallelShare00.Check81Part1
import ParallelShareApplicability.ParallelShare00.Check81Part2
import ParallelShareApplicability.ParallelShare00.Check81Part3
import ParallelShareApplicability.ParallelShare00.Check81Part4
import ParallelShareApplicability.ParallelShare00.Check81Part5
import ParallelShareApplicability.ParallelShare00.Check81Part6
import ParallelShareApplicability.ParallelShare00.Check81Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts81Refined : List (List Tag × List (List Nat)) := [((tags81.drop 0).take 16, (raw81.drop 0).take 16), ((tags81.drop 16).take 16, (raw81.drop 16).take 16), ((tags81.drop 32).take 16, (raw81.drop 32).take 16), ((tags81.drop 48).take 16, (raw81.drop 48).take 16), ((tags81.drop 64).take 16, (raw81.drop 64).take 16), ((tags81.drop 80).take 16, (raw81.drop 80).take 16), ((tags81.drop 96).take 16, (raw81.drop 96).take 16), ((tags81.drop 112).take 16, (raw81.drop 112).take 16)]

theorem check81 : checkRaw oldMeaning ctrs window terms meaning 20 tags81 raw81 = true := by
  have ht : parts81Refined.flatMap Prod.fst = tags81 := by rfl
  have hr : parts81Refined.flatMap Prod.snd = raw81 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts81Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check81Part0
  · exact check81Part1
  · exact check81Part2
  · exact check81Part3
  · exact check81Part4
  · exact check81Part5
  · exact check81Part6
  · exact check81Part7
end Snake9.LocalWindow.ParallelShare00Applicability
