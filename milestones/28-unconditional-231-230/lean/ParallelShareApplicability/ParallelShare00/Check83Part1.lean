import ParallelShareApplicability.ParallelShare00.Data
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

theorem check83Part1 : checkRaw oldMeaning ctrs window terms meaning 20 ((tags83.drop 16).take 16) ((raw83.drop 16).take 16) = true := by decide +kernel
end Snake9.LocalWindow.ParallelShare00Applicability
