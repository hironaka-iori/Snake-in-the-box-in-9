import DfsDecide
import DfsBankData
import DfsBankCert144v2_j16c0

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem keep144v2_18 : search2 (oriented 18)[143]! (banFrom (fun i => (oriented 18)[i]!) 143) 49 = false := by
  rw [show (oriented 18)[143]! = 229 from by decide +kernel,
    show banFrom (fun i => (oriented 18)[i]!) 143 = 11162246935463076903917279285664150499828350328657845340440412607889563842449349201739701508035310156683757688253502754869421867299951244885220756136394751 from by decide +kernel]
  exact keep144v2_16_lit

end Snake9.Dfs
