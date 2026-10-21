import ParallelShareApplicability.ParallelShare00.Check62Part0
import ParallelShareApplicability.ParallelShare00.Check62Part1
import ParallelShareApplicability.ParallelShare00.Check62Part2
import ParallelShareApplicability.ParallelShare00.Check62Part3
import ParallelShareApplicability.ParallelShare00.Check62Part4
import ParallelShareApplicability.ParallelShare00.Check62Part5
import ParallelShareApplicability.ParallelShare00.Check62Part6
import ParallelShareApplicability.ParallelShare00.Check62Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts62Refined : List (List Tag × List (List Nat)) := [((tags62.drop 0).take 16, (raw62.drop 0).take 16), ((tags62.drop 16).take 16, (raw62.drop 16).take 16), ((tags62.drop 32).take 16, (raw62.drop 32).take 16), ((tags62.drop 48).take 16, (raw62.drop 48).take 16), ((tags62.drop 64).take 16, (raw62.drop 64).take 16), ((tags62.drop 80).take 16, (raw62.drop 80).take 16), ((tags62.drop 96).take 16, (raw62.drop 96).take 16), ((tags62.drop 112).take 16, (raw62.drop 112).take 16)]

theorem check62 : checkRaw oldMeaning ctrs window terms meaning 20 tags62 raw62 = true := by
  have ht : parts62Refined.flatMap Prod.fst = tags62 := by rfl
  have hr : parts62Refined.flatMap Prod.snd = raw62 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts62Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check62Part0
  · exact check62Part1
  · exact check62Part2
  · exact check62Part3
  · exact check62Part4
  · exact check62Part5
  · exact check62Part6
  · exact check62Part7
end Snake9.LocalWindow.ParallelShare00Applicability
