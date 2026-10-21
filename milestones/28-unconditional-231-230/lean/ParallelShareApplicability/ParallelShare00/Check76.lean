import ParallelShareApplicability.ParallelShare00.Check76Part0
import ParallelShareApplicability.ParallelShare00.Check76Part1
import ParallelShareApplicability.ParallelShare00.Check76Part2
import ParallelShareApplicability.ParallelShare00.Check76Part3
import ParallelShareApplicability.ParallelShare00.Check76Part4
import ParallelShareApplicability.ParallelShare00.Check76Part5
import ParallelShareApplicability.ParallelShare00.Check76Part6
import ParallelShareApplicability.ParallelShare00.Check76Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts76Refined : List (List Tag × List (List Nat)) := [((tags76.drop 0).take 16, (raw76.drop 0).take 16), ((tags76.drop 16).take 16, (raw76.drop 16).take 16), ((tags76.drop 32).take 16, (raw76.drop 32).take 16), ((tags76.drop 48).take 16, (raw76.drop 48).take 16), ((tags76.drop 64).take 16, (raw76.drop 64).take 16), ((tags76.drop 80).take 16, (raw76.drop 80).take 16), ((tags76.drop 96).take 16, (raw76.drop 96).take 16), ((tags76.drop 112).take 16, (raw76.drop 112).take 16)]

theorem check76 : checkRaw oldMeaning ctrs window terms meaning 20 tags76 raw76 = true := by
  have ht : parts76Refined.flatMap Prod.fst = tags76 := by rfl
  have hr : parts76Refined.flatMap Prod.snd = raw76 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts76Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check76Part0
  · exact check76Part1
  · exact check76Part2
  · exact check76Part3
  · exact check76Part4
  · exact check76Part5
  · exact check76Part6
  · exact check76Part7
end Snake9.LocalWindow.ParallelShare00Applicability
