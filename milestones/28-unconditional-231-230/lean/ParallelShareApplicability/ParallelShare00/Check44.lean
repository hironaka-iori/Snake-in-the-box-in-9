import ParallelShareApplicability.ParallelShare00.Check44Part0
import ParallelShareApplicability.ParallelShare00.Check44Part1
import ParallelShareApplicability.ParallelShare00.Check44Part2
import ParallelShareApplicability.ParallelShare00.Check44Part3
import ParallelShareApplicability.ParallelShare00.Check44Part4
import ParallelShareApplicability.ParallelShare00.Check44Part5
import ParallelShareApplicability.ParallelShare00.Check44Part6
import ParallelShareApplicability.ParallelShare00.Check44Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts44Refined : List (List Tag × List (List Nat)) := [((tags44.drop 0).take 16, (raw44.drop 0).take 16), ((tags44.drop 16).take 16, (raw44.drop 16).take 16), ((tags44.drop 32).take 16, (raw44.drop 32).take 16), ((tags44.drop 48).take 16, (raw44.drop 48).take 16), ((tags44.drop 64).take 16, (raw44.drop 64).take 16), ((tags44.drop 80).take 16, (raw44.drop 80).take 16), ((tags44.drop 96).take 16, (raw44.drop 96).take 16), ((tags44.drop 112).take 16, (raw44.drop 112).take 16)]

theorem check44 : checkRaw oldMeaning ctrs window terms meaning 20 tags44 raw44 = true := by
  have ht : parts44Refined.flatMap Prod.fst = tags44 := by rfl
  have hr : parts44Refined.flatMap Prod.snd = raw44 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts44Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check44Part0
  · exact check44Part1
  · exact check44Part2
  · exact check44Part3
  · exact check44Part4
  · exact check44Part5
  · exact check44Part6
  · exact check44Part7
end Snake9.LocalWindow.ParallelShare00Applicability
