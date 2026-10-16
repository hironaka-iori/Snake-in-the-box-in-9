import DfsDecide
import DfsBankData
import DfsBankCert144v2_j0c0

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem keep144v2_2 : search2 (oriented 2)[143]! (banFrom (fun i => (oriented 2)[i]!) 143) 49 = false := by
  rw [show (oriented 2)[143]! = 167 from by decide +kernel,
    show banFrom (fun i => (oriented 2)[i]!) 143 = 769316773092845772657183861855200495970159358177386022649298068791568134272951477207109660716366018368746857685788474121590960793871227448075756974899199 from by decide +kernel]
  exact keep144v2_0_lit

end Snake9.Dfs
