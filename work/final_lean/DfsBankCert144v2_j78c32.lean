import DfsDecide
import DfsBankData
import DfsBankCert144v2_j78c31

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem keep144v2_204 : search2 (oriented 204)[143]! (banFrom (fun i => (oriented 204)[i]!) 143) 49 = false := by
  rw [show (oriented 204)[143]! = 391 from by decide +kernel,
    show banFrom (fun i => (oriented 204)[i]!) 143 = 13407807928239136420970781354009551728869512619862650640186376446770266348702643461127094134052225204733102390785357204548233947076155402242062291293962239 from by decide +kernel]
  exact keep144v2_78_lit

end Snake9.Dfs
