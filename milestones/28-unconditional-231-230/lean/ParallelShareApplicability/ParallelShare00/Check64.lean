import ParallelShareApplicability.ParallelShare00.Check64Part0
import ParallelShareApplicability.ParallelShare00.Check64Part1
import ParallelShareApplicability.ParallelShare00.Check64Part2
import ParallelShareApplicability.ParallelShare00.Check64Part3
import ParallelShareApplicability.ParallelShare00.Check64Part4
import ParallelShareApplicability.ParallelShare00.Check64Part5
import ParallelShareApplicability.ParallelShare00.Check64Part6
import ParallelShareApplicability.ParallelShare00.Check64Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts64Refined : List (List Tag × List (List Nat)) := [((tags64.drop 0).take 16, (raw64.drop 0).take 16), ((tags64.drop 16).take 16, (raw64.drop 16).take 16), ((tags64.drop 32).take 16, (raw64.drop 32).take 16), ((tags64.drop 48).take 16, (raw64.drop 48).take 16), ((tags64.drop 64).take 16, (raw64.drop 64).take 16), ((tags64.drop 80).take 16, (raw64.drop 80).take 16), ((tags64.drop 96).take 16, (raw64.drop 96).take 16), ((tags64.drop 112).take 16, (raw64.drop 112).take 16)]

theorem check64 : checkRaw oldMeaning ctrs window terms meaning 20 tags64 raw64 = true := by
  have ht : parts64Refined.flatMap Prod.fst = tags64 := by rfl
  have hr : parts64Refined.flatMap Prod.snd = raw64 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts64Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check64Part0
  · exact check64Part1
  · exact check64Part2
  · exact check64Part3
  · exact check64Part4
  · exact check64Part5
  · exact check64Part6
  · exact check64Part7
end Snake9.LocalWindow.ParallelShare00Applicability
