import ParallelShareApplicability.ParallelShare00.Check55Part0
import ParallelShareApplicability.ParallelShare00.Check55Part1
import ParallelShareApplicability.ParallelShare00.Check55Part2
import ParallelShareApplicability.ParallelShare00.Check55Part3
import ParallelShareApplicability.ParallelShare00.Check55Part4
import ParallelShareApplicability.ParallelShare00.Check55Part5
import ParallelShareApplicability.ParallelShare00.Check55Part6
import ParallelShareApplicability.ParallelShare00.Check55Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts55Refined : List (List Tag × List (List Nat)) := [((tags55.drop 0).take 16, (raw55.drop 0).take 16), ((tags55.drop 16).take 16, (raw55.drop 16).take 16), ((tags55.drop 32).take 16, (raw55.drop 32).take 16), ((tags55.drop 48).take 16, (raw55.drop 48).take 16), ((tags55.drop 64).take 16, (raw55.drop 64).take 16), ((tags55.drop 80).take 16, (raw55.drop 80).take 16), ((tags55.drop 96).take 16, (raw55.drop 96).take 16), ((tags55.drop 112).take 16, (raw55.drop 112).take 16)]

theorem check55 : checkRaw oldMeaning ctrs window terms meaning 20 tags55 raw55 = true := by
  have ht : parts55Refined.flatMap Prod.fst = tags55 := by rfl
  have hr : parts55Refined.flatMap Prod.snd = raw55 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts55Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check55Part0
  · exact check55Part1
  · exact check55Part2
  · exact check55Part3
  · exact check55Part4
  · exact check55Part5
  · exact check55Part6
  · exact check55Part7
end Snake9.LocalWindow.ParallelShare00Applicability
