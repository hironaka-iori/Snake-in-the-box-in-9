import ContextAssignmentLiteCore

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.ContextLite92
theorem chunk_16 : chunkCheck 320 20 = true := by decide +kernel
#print axioms chunk_16
end Snake9.ContextLite92
