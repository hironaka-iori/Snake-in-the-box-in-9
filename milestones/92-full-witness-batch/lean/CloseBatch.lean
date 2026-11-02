import ContextAssignmentChecks
import DefinedProofGraph
import Witness000Checks
import Witness001Checks
import Witness002Checks
import Witness003Checks
import Witness004Checks
import Witness005Checks
import Witness006Checks
import Witness007Checks
import Witness008Checks
import Witness009Checks
import Witness010Checks
import Witness011Checks
import Witness012Checks
import Witness013Checks
import Witness014Checks
import Witness015Checks
import Witness016Checks
import Witness017Checks
import Witness018Checks
import Witness019Checks
import Witness020Checks
import Witness021Checks
import Witness022Checks
import Witness023Checks
import Witness024Checks
import Witness025Checks
import Witness026Checks
import Witness027Checks
import Witness028Checks
import Witness029Checks
import Witness030Checks
import Witness031Checks
import Witness032Checks
import Witness033Checks
import Witness034Checks
import Witness035Checks
import Witness036Checks
import Witness037Checks
import Witness038Checks
import Witness039Checks
import Witness040Checks
import Witness041Checks
import Witness042Checks
import Witness043Checks
import Witness044Checks
import Witness045Checks
import Witness046Checks
import Witness047Checks
import Witness048Checks
import Witness049Checks
import Witness050Checks
import Witness051Checks
import Witness052Checks
import Witness053Checks
import Witness054Checks
import Witness055Checks
import Witness056Checks
import Witness057Checks
import Witness058Checks
import Witness059Checks
import Witness060Checks
import Witness061Checks
import Witness062Checks
import Witness063Checks
import Witness064Checks
import Witness065Checks
import Witness066Checks
import Witness067Checks
import Witness068Checks
import Witness069Checks
import Witness070Checks
import Witness071Checks
import Witness072Checks
import Witness073Checks
import Witness074Checks
import Witness075Checks
import Witness076Checks
import Witness077Checks
import Witness078Checks
import Witness079Checks
import Witness080Checks
import Witness081Checks
import Witness082Checks
import Witness083Checks
import Witness084Checks
import Witness085Checks
import Witness086Checks
import Witness087Checks
import Witness088Checks
import Witness089Checks
import Witness090Checks
import Witness091Checks
import Witness092Checks
import Witness093Checks
import Witness094Checks
import Witness095Checks
import Witness096Checks
import Witness097Checks
import Witness098Checks
import Witness099Checks
import Witness100Checks
import Witness101Checks
import Witness102Checks
import Witness103Checks
import Witness104Checks
import Witness105Checks
import Witness106Checks
import Witness107Checks
import Witness108Checks
import Witness109Checks
import Witness110Checks
import Witness111Checks
import Witness112Checks
import Witness113Checks
import Witness114Checks
import Witness115Checks
import Witness116Checks
import Witness117Checks
import Witness118Checks
import Witness119Checks
import Witness120Checks
import Witness121Checks
import Witness122Checks
import Witness123Checks
import Witness124Checks
import Witness125Checks
import Witness126Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Retained87

open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.GraphWalk78

theorem retained_class_family : ClassMembershipFamily retainedDiagram := by
  intro cls hcls di q code hm hq hc hk
  interval_cases cls
  · exact class000_context_membership di q code hm hc hk
  · exact class001_context_membership di q code hm hc hk
  · exact class002_context_membership di q code hm hc hk
  · exact class003_context_membership di q code hm hc hk
  · exact class004_context_membership di q code hm hc hk
  · exact class005_context_membership di q code hm hc hk
  · exact class006_context_membership di q code hm hc hk
  · exact class007_context_membership di q code hm hc hk
  · exact class008_context_membership di q code hm hc hk
  · exact class009_context_membership di q code hm hc hk
  · exact class010_context_membership di q code hm hc hk
  · exact class011_context_membership di q code hm hc hk
  · exact class012_context_membership di q code hm hc hk
  · exact class013_context_membership di q code hm hc hk
  · exact class014_context_membership di q code hm hc hk
  · exact class015_context_membership di q code hm hc hk
  · exact class016_context_membership di q code hm hc hk
  · exact class017_context_membership di q code hm hc hk
  · exact class018_context_membership di q code hm hc hk
  · exact class019_context_membership di q code hm hc hk
  · exact class020_context_membership di q code hm hc hk
  · exact class021_context_membership di q code hm hc hk
  · exact class022_context_membership di q code hm hc hk
  · exact class023_context_membership di q code hm hc hk
  · exact class024_context_membership di q code hm hc hk
  · exact class025_context_membership di q code hm hc hk
  · exact class026_context_membership di q code hm hc hk
  · exact class027_context_membership di q code hm hc hk
  · exact class028_context_membership di q code hm hc hk
  · exact class029_context_membership di q code hm hc hk
  · exact class030_context_membership di q code hm hc hk
  · exact class031_context_membership di q code hm hc hk
  · exact class032_context_membership di q code hm hc hk
  · exact class033_context_membership di q code hm hc hk
  · exact class034_context_membership di q code hm hc hk
  · exact class035_context_membership di q code hm hc hk
  · exact class036_context_membership di q code hm hc hk
  · exact class037_context_membership di q code hm hc hk
  · exact class038_context_membership di q code hm hc hk
  · exact class039_context_membership di q code hm hc hk
  · exact class040_context_membership di q code hm hc hk
  · exact class041_context_membership di q code hm hc hk
  · exact class042_context_membership di q code hm hc hk
  · exact class043_context_membership di q code hm hc hk
  · exact class044_context_membership di q code hm hc hk
  · exact class045_context_membership di q code hm hc hk
  · exact class046_context_membership di q code hm hc hk
  · exact class047_context_membership di q code hm hc hk
  · exact class048_context_membership di q code hm hc hk
  · exact class049_context_membership di q code hm hc hk
  · exact class050_context_membership di q code hm hc hk
  · exact class051_context_membership di q code hm hc hk
  · exact class052_context_membership di q code hm hc hk
  · exact class053_context_membership di q code hm hc hk
  · exact class054_context_membership di q code hm hc hk
  · exact class055_context_membership di q code hm hc hk
  · exact class056_context_membership di q code hm hc hk
  · exact class057_context_membership di q code hm hc hk
  · exact class058_context_membership di q code hm hc hk
  · exact class059_context_membership di q code hm hc hk
  · exact class060_context_membership di q code hm hc hk
  · exact class061_context_membership di q code hm hc hk
  · exact class062_context_membership di q code hm hc hk
  · exact class063_context_membership di q code hm hc hk
  · exact class064_context_membership di q code hm hc hk
  · exact class065_context_membership di q code hm hc hk
  · exact class066_context_membership di q code hm hc hk
  · exact class067_context_membership di q code hm hc hk
  · exact class068_context_membership di q code hm hc hk
  · exact class069_context_membership di q code hm hc hk
  · exact class070_context_membership di q code hm hc hk
  · exact class071_context_membership di q code hm hc hk
  · exact class072_context_membership di q code hm hc hk
  · exact class073_context_membership di q code hm hc hk
  · exact class074_context_membership di q code hm hc hk
  · exact class075_context_membership di q code hm hc hk
  · exact class076_context_membership di q code hm hc hk
  · exact class077_context_membership di q code hm hc hk
  · exact class078_context_membership di q code hm hc hk
  · exact class079_context_membership di q code hm hc hk
  · exact class080_context_membership di q code hm hc hk
  · exact class081_context_membership di q code hm hc hk
  · exact class082_context_membership di q code hm hc hk
  · exact class083_context_membership di q code hm hc hk
  · exact class084_context_membership di q code hm hc hk
  · exact class085_context_membership di q code hm hc hk
  · exact class086_context_membership di q code hm hc hk
  · exact class087_context_membership di q code hm hc hk
  · exact class088_context_membership di q code hm hc hk
  · exact class089_context_membership di q code hm hc hk
  · exact class090_context_membership di q code hm hc hk
  · exact class091_context_membership di q code hm hc hk
  · exact class092_context_membership di q code hm hc hk
  · exact class093_context_membership di q code hm hc hk
  · exact class094_context_membership di q code hm hc hk
  · exact class095_context_membership di q code hm hc hk
  · exact class096_context_membership di q code hm hc hk
  · exact class097_context_membership di q code hm hc hk
  · exact class098_context_membership di q code hm hc hk
  · exact class099_context_membership di q code hm hc hk
  · exact class100_context_membership di q code hm hc hk
  · exact class101_context_membership di q code hm hc hk
  · exact class102_context_membership di q code hm hc hk
  · exact class103_context_membership di q code hm hc hk
  · exact class104_context_membership di q code hm hc hk
  · exact class105_context_membership di q code hm hc hk
  · exact class106_context_membership di q code hm hc hk
  · exact class107_context_membership di q code hm hc hk
  · exact class108_context_membership di q code hm hc hk
  · exact class109_context_membership di q code hm hc hk
  · exact class110_context_membership di q code hm hc hk
  · exact class111_context_membership di q code hm hc hk
  · exact class112_context_membership di q code hm hc hk
  · exact class113_context_membership di q code hm hc hk
  · exact class114_context_membership di q code hm hc hk
  · exact class115_context_membership di q code hm hc hk
  · exact class116_context_membership di q code hm hc hk
  · exact class117_context_membership di q code hm hc hk
  · exact class118_context_membership di q code hm hc hk
  · exact class119_context_membership di q code hm hc hk
  · exact class120_context_membership di q code hm hc hk
  · exact class121_context_membership di q code hm hc hk
  · exact class122_context_membership di q code hm hc hk
  · exact class123_context_membership di q code hm hc hk
  · exact class124_context_membership di q code hm hc hk
  · exact class125_context_membership di q code hm hc hk
  · exact class126_context_membership di q code hm hc hk

theorem retained_numeric_diagram (q di code : Nat) (hd : di < 505)
    (hk : numericKeep q di code = true) :
    Assigned di q ∧ diagramEval retainedDiagram (recordedClassRoot (chosenClass di q)) (digits code) = true :=
  numeric_context_membership retainedDiagram retained_class_family q di code hd hk

theorem retained_defined_walk (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    {m : Nat} (p : Snake m) :
    ∃ edge : Fin (m-8) → Fin (Snake9.DefinedGraph92.rows retainedDiagram).size, ∀ i,
      (Snake9.DefinedGraph92.sources retainedDiagram).toList[(edge i).val]? = some (actualState p i.val) ∧
      (Snake9.DefinedGraph92.targets retainedDiagram).toList[(edge i).val]? = some (actualState p (i.val+1)) :=
  Snake9.DefinedGraph92.defined_actual_walk retainedDiagram retained_class_family assignment_checked h235 h236 p

#print axioms retained_class_family
#print axioms retained_numeric_diagram
#print axioms retained_defined_walk
end Snake9.Batch92
