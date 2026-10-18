import DfsDecide
import DfsBankData
import DfsBankCert144v2_j10c0

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem keep144v2_12 : search2 (oriented 12)[143]! (banFrom (fun i => (oriented 12)[i]!) 143) 49 = false := by
  rw [show (oriented 12)[143]! = 233 from by decide +kernel,
    show banFrom (fun i => (oriented 12)[i]!) 143 = 12641402074989973177217980071922586091295610406165776424423382391484440967600306220875162603621492803613428974767105287942761153725141035503356975672983551 from by decide +kernel]
  exact keep144v2_10_lit

end Snake9.Dfs
