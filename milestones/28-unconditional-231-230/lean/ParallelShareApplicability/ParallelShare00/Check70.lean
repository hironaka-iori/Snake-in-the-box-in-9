import ParallelShareApplicability.ParallelShare00.Check70Part0
import ParallelShareApplicability.ParallelShare00.Check70Part1
import ParallelShareApplicability.ParallelShare00.Check70Part2
import ParallelShareApplicability.ParallelShare00.Check70Part3
import ParallelShareApplicability.ParallelShare00.Check70Part4
import ParallelShareApplicability.ParallelShare00.Check70Part5
import ParallelShareApplicability.ParallelShare00.Check70Part6
import ParallelShareApplicability.ParallelShare00.Check70Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts70Refined : List (List Tag × List (List Nat)) := [((tags70.drop 0).take 16, (raw70.drop 0).take 16), ((tags70.drop 16).take 16, (raw70.drop 16).take 16), ((tags70.drop 32).take 16, (raw70.drop 32).take 16), ((tags70.drop 48).take 16, (raw70.drop 48).take 16), ((tags70.drop 64).take 16, (raw70.drop 64).take 16), ((tags70.drop 80).take 16, (raw70.drop 80).take 16), ((tags70.drop 96).take 16, (raw70.drop 96).take 16), ((tags70.drop 112).take 16, (raw70.drop 112).take 16)]

theorem check70 : checkRaw oldMeaning ctrs window terms meaning 20 tags70 raw70 = true := by
  have ht : parts70Refined.flatMap Prod.fst = tags70 := by rfl
  have hr : parts70Refined.flatMap Prod.snd = raw70 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts70Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check70Part0
  · exact check70Part1
  · exact check70Part2
  · exact check70Part3
  · exact check70Part4
  · exact check70Part5
  · exact check70Part6
  · exact check70Part7
end Snake9.LocalWindow.ParallelShare00Applicability
