import ParallelShareApplicability.ParallelShare00.Check63Part0
import ParallelShareApplicability.ParallelShare00.Check63Part1
import ParallelShareApplicability.ParallelShare00.Check63Part2
import ParallelShareApplicability.ParallelShare00.Check63Part3
import ParallelShareApplicability.ParallelShare00.Check63Part4
import ParallelShareApplicability.ParallelShare00.Check63Part5
import ParallelShareApplicability.ParallelShare00.Check63Part6
import ParallelShareApplicability.ParallelShare00.Check63Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts63Refined : List (List Tag × List (List Nat)) := [((tags63.drop 0).take 16, (raw63.drop 0).take 16), ((tags63.drop 16).take 16, (raw63.drop 16).take 16), ((tags63.drop 32).take 16, (raw63.drop 32).take 16), ((tags63.drop 48).take 16, (raw63.drop 48).take 16), ((tags63.drop 64).take 16, (raw63.drop 64).take 16), ((tags63.drop 80).take 16, (raw63.drop 80).take 16), ((tags63.drop 96).take 16, (raw63.drop 96).take 16), ((tags63.drop 112).take 16, (raw63.drop 112).take 16)]

theorem check63 : checkRaw oldMeaning ctrs window terms meaning 20 tags63 raw63 = true := by
  have ht : parts63Refined.flatMap Prod.fst = tags63 := by rfl
  have hr : parts63Refined.flatMap Prod.snd = raw63 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts63Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check63Part0
  · exact check63Part1
  · exact check63Part2
  · exact check63Part3
  · exact check63Part4
  · exact check63Part5
  · exact check63Part6
  · exact check63Part7
end Snake9.LocalWindow.ParallelShare00Applicability
