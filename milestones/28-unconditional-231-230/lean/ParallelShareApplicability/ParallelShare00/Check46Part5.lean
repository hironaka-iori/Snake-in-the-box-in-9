import ParallelShareApplicability.ParallelShare00.Data
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

theorem check46Part5 : checkRaw oldMeaning ctrs window terms meaning 20 ((tags46.drop 80).take 16) ((raw46.drop 80).take 16) = true := by decide +kernel
end Snake9.LocalWindow.ParallelShare00Applicability
