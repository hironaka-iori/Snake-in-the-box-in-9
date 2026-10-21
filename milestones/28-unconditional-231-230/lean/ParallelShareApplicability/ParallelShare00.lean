import ParallelShareApplicability.ParallelShare00.Check0
import ParallelShareApplicability.ParallelShare00.Check1
import ParallelShareApplicability.ParallelShare00.Check2
import ParallelShareApplicability.ParallelShare00.Check3
import ParallelShareApplicability.ParallelShare00.Check4
import ParallelShareApplicability.ParallelShare00.Check5
import ParallelShareApplicability.ParallelShare00.Check6
import ParallelShareApplicability.ParallelShare00.Check7
import ParallelShareApplicability.ParallelShare00.Check8
import ParallelShareApplicability.ParallelShare00.Check9
import ParallelShareApplicability.ParallelShare00.Check10
import ParallelShareApplicability.ParallelShare00.Check11
import ParallelShareApplicability.ParallelShare00.Check12
import ParallelShareApplicability.ParallelShare00.Check13
import ParallelShareApplicability.ParallelShare00.Check14
import ParallelShareApplicability.ParallelShare00.Check15
import ParallelShareApplicability.ParallelShare00.Check16
import ParallelShareApplicability.ParallelShare00.Check17
import ParallelShareApplicability.ParallelShare00.Check18
import ParallelShareApplicability.ParallelShare00.Check19
import ParallelShareApplicability.ParallelShare00.Check20
import ParallelShareApplicability.ParallelShare00.Check21
import ParallelShareApplicability.ParallelShare00.Check22
import ParallelShareApplicability.ParallelShare00.Check23
import ParallelShareApplicability.ParallelShare00.Check24
import ParallelShareApplicability.ParallelShare00.Check25
import ParallelShareApplicability.ParallelShare00.Check26
import ParallelShareApplicability.ParallelShare00.Check27
import ParallelShareApplicability.ParallelShare00.Check28
import ParallelShareApplicability.ParallelShare00.Check29
import ParallelShareApplicability.ParallelShare00.Check30
import ParallelShareApplicability.ParallelShare00.Check31
import ParallelShareApplicability.ParallelShare00.Check32
import ParallelShareApplicability.ParallelShare00.Check33
import ParallelShareApplicability.ParallelShare00.Check34
import ParallelShareApplicability.ParallelShare00.Check35
import ParallelShareApplicability.ParallelShare00.Check36
import ParallelShareApplicability.ParallelShare00.Check37
import ParallelShareApplicability.ParallelShare00.Check38
import ParallelShareApplicability.ParallelShare00.Check39
import ParallelShareApplicability.ParallelShare00.Check40
import ParallelShareApplicability.ParallelShare00.Check41
import ParallelShareApplicability.ParallelShare00.Check42
import ParallelShareApplicability.ParallelShare00.Check43
import ParallelShareApplicability.ParallelShare00.Check44
import ParallelShareApplicability.ParallelShare00.Check45
import ParallelShareApplicability.ParallelShare00.Check46
import ParallelShareApplicability.ParallelShare00.Check47
import ParallelShareApplicability.ParallelShare00.Check48
import ParallelShareApplicability.ParallelShare00.Check49
import ParallelShareApplicability.ParallelShare00.Check50
import ParallelShareApplicability.ParallelShare00.Check51
import ParallelShareApplicability.ParallelShare00.Check52
import ParallelShareApplicability.ParallelShare00.Check53
import ParallelShareApplicability.ParallelShare00.Check54
import ParallelShareApplicability.ParallelShare00.Check55
import ParallelShareApplicability.ParallelShare00.Check56
import ParallelShareApplicability.ParallelShare00.Check57
import ParallelShareApplicability.ParallelShare00.Check58
import ParallelShareApplicability.ParallelShare00.Check59
import ParallelShareApplicability.ParallelShare00.Check60
import ParallelShareApplicability.ParallelShare00.Check61
import ParallelShareApplicability.ParallelShare00.Check62
import ParallelShareApplicability.ParallelShare00.Check63
import ParallelShareApplicability.ParallelShare00.Check64
import ParallelShareApplicability.ParallelShare00.Check65
import ParallelShareApplicability.ParallelShare00.Check66
import ParallelShareApplicability.ParallelShare00.Check67
import ParallelShareApplicability.ParallelShare00.Check68
import ParallelShareApplicability.ParallelShare00.Check69
import ParallelShareApplicability.ParallelShare00.Check70
import ParallelShareApplicability.ParallelShare00.Check71
import ParallelShareApplicability.ParallelShare00.Check72
import ParallelShareApplicability.ParallelShare00.Check73
import ParallelShareApplicability.ParallelShare00.Check74
import ParallelShareApplicability.ParallelShare00.Check75
import ParallelShareApplicability.ParallelShare00.Check76
import ParallelShareApplicability.ParallelShare00.Check77
import ParallelShareApplicability.ParallelShare00.Check78
import ParallelShareApplicability.ParallelShare00.Check79
import ParallelShareApplicability.ParallelShare00.Check80
import ParallelShareApplicability.ParallelShare00.Check81
import ParallelShareApplicability.ParallelShare00.Check82
import ParallelShareApplicability.ParallelShare00.Check83
import ParallelShareApplicability.ParallelShare00.Check84
import ParallelShareApplicability.ParallelShare00.Check85
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts : List (List ParallelShareCertificate.Tag × List (List Nat)) := [(tags0, raw0), (tags1, raw1), (tags2, raw2), (tags3, raw3), (tags4, raw4), (tags5, raw5), (tags6, raw6), (tags7, raw7), (tags8, raw8), (tags9, raw9), (tags10, raw10), (tags11, raw11), (tags12, raw12), (tags13, raw13), (tags14, raw14), (tags15, raw15), (tags16, raw16), (tags17, raw17), (tags18, raw18), (tags19, raw19), (tags20, raw20), (tags21, raw21), (tags22, raw22), (tags23, raw23), (tags24, raw24), (tags25, raw25), (tags26, raw26), (tags27, raw27), (tags28, raw28), (tags29, raw29), (tags30, raw30), (tags31, raw31), (tags32, raw32), (tags33, raw33), (tags34, raw34), (tags35, raw35), (tags36, raw36), (tags37, raw37), (tags38, raw38), (tags39, raw39), (tags40, raw40), (tags41, raw41), (tags42, raw42), (tags43, raw43), (tags44, raw44), (tags45, raw45), (tags46, raw46), (tags47, raw47), (tags48, raw48), (tags49, raw49), (tags50, raw50), (tags51, raw51), (tags52, raw52), (tags53, raw53), (tags54, raw54), (tags55, raw55), (tags56, raw56), (tags57, raw57), (tags58, raw58), (tags59, raw59), (tags60, raw60), (tags61, raw61), (tags62, raw62), (tags63, raw63), (tags64, raw64), (tags65, raw65), (tags66, raw66), (tags67, raw67), (tags68, raw68), (tags69, raw69), (tags70, raw70), (tags71, raw71), (tags72, raw72), (tags73, raw73), (tags74, raw74), (tags75, raw75), (tags76, raw76), (tags77, raw77), (tags78, raw78), (tags79, raw79), (tags80, raw80), (tags81, raw81), (tags82, raw82), (tags83, raw83), (tags84, raw84), (tags85, raw85)]
def tags : List ParallelShareCertificate.Tag := parts.flatMap Prod.fst
theorem exact_raw : parts.flatMap Prod.snd = ParallelShare00.raw := by decide +kernel
theorem checkedRaw : checkRaw oldMeaning ctrs window terms meaning 20 tags ParallelShare00.raw = true := by
  rw [← exact_raw]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
  · exact check21
  · exact check22
  · exact check23
  · exact check24
  · exact check25
  · exact check26
  · exact check27
  · exact check28
  · exact check29
  · exact check30
  · exact check31
  · exact check32
  · exact check33
  · exact check34
  · exact check35
  · exact check36
  · exact check37
  · exact check38
  · exact check39
  · exact check40
  · exact check41
  · exact check42
  · exact check43
  · exact check44
  · exact check45
  · exact check46
  · exact check47
  · exact check48
  · exact check49
  · exact check50
  · exact check51
  · exact check52
  · exact check53
  · exact check54
  · exact check55
  · exact check56
  · exact check57
  · exact check58
  · exact check59
  · exact check60
  · exact check61
  · exact check62
  · exact check63
  · exact check64
  · exact check65
  · exact check66
  · exact check67
  · exact check68
  · exact check69
  · exact check70
  · exact check71
  · exact check72
  · exact check73
  · exact check74
  · exact check75
  · exact check76
  · exact check77
  · exact check78
  · exact check79
  · exact check80
  · exact check81
  · exact check82
  · exact check83
  · exact check84
  · exact check85
theorem checked : checkAll oldMeaning ctrs window bounds terms meaning 20 tags ParallelShare00.raw = true := by
  simp only [checkAll, countersChecked, termsChecked, checkedRaw, Bool.true_and]
theorem sat (S E : Nat → Bool) (ax : AxiomsP S E window (centresOf window bounds) 20) :
    ∃ tau, cnfTrue tau ParallelShare00.cnf = true :=
  ⟨ParallelShareClauses.assignment (Tags.tau S E oldMeaning ctrs) S terms meaning,
    sound oldMeaning ctrs window bounds terms meaning 20 tags ParallelShare00.raw checked S E ax⟩
theorem refuted_of_unsat (hu : Unsat ParallelShare00.cnf) : RefutedParallel window bounds 20 :=
  refuted_of_check oldMeaning ctrs window bounds terms meaning 20 tags ParallelShare00.raw checked hu
#print axioms sat
#print axioms refuted_of_unsat
end Snake9.LocalWindow.ParallelShare00Applicability
