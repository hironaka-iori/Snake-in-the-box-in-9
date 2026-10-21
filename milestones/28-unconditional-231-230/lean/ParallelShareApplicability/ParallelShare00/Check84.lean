import ParallelShareApplicability.ParallelShare00.Check84Part0
import ParallelShareApplicability.ParallelShare00.Check84Part1
import ParallelShareApplicability.ParallelShare00.Check84Part2
import ParallelShareApplicability.ParallelShare00.Check84Part3
import ParallelShareApplicability.ParallelShare00.Check84Part4
import ParallelShareApplicability.ParallelShare00.Check84Part5
import ParallelShareApplicability.ParallelShare00.Check84Part6
import ParallelShareApplicability.ParallelShare00.Check84Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts84Refined : List (List Tag × List (List Nat)) := [((tags84.drop 0).take 16, (raw84.drop 0).take 16), ((tags84.drop 16).take 16, (raw84.drop 16).take 16), ((tags84.drop 32).take 16, (raw84.drop 32).take 16), ((tags84.drop 48).take 16, (raw84.drop 48).take 16), ((tags84.drop 64).take 16, (raw84.drop 64).take 16), ((tags84.drop 80).take 16, (raw84.drop 80).take 16), ((tags84.drop 96).take 16, (raw84.drop 96).take 16), ((tags84.drop 112).take 16, (raw84.drop 112).take 16)]

theorem check84 : checkRaw oldMeaning ctrs window terms meaning 20 tags84 raw84 = true := by
  have ht : parts84Refined.flatMap Prod.fst = tags84 := by rfl
  have hr : parts84Refined.flatMap Prod.snd = raw84 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts84Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check84Part0
  · exact check84Part1
  · exact check84Part2
  · exact check84Part3
  · exact check84Part4
  · exact check84Part5
  · exact check84Part6
  · exact check84Part7
end Snake9.LocalWindow.ParallelShare00Applicability
