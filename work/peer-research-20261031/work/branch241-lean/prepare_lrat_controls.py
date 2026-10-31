"""Small format controls for legitimate online Lean: positive and expected-negative."""
from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parent;W=18;FLAG=1<<17
prefix=(H/'PeerLratSmokeStandalone.lean').read_text(encoding='utf-8')
def pack(ws):return sum(x<<(W*i) for i,x in enumerate(ws))
def code(l):return 2*abs(l)+(l<0)
def block(name,clauses,slots,height,lemmas,final):
 raw='['+', '.join('['+', '.join(str(code(l)) for l in c)+']' for c in clauses)+']'
 proof='['+', '.join('nat_lit '+str(pack([k]+[abs(l)+(5000 if l<0 else 0)+1 for l in c]+[0]+hints+[0])) for k,c,hints in lemmas)+']'
 return f'''namespace {name}
def raw : List (List Nat) := {raw}
def cnf := raw.map (List.map decodeLit)
noncomputable def start : Tree := loadRaw (perf {height} 0) raw {slots}
noncomputable def proof : List Nat := {proof}
theorem checked : andB (check2 start (perf {height} 0) proof) (hasEmpty (replay start proof) {final}) = true := by decide +kernel
theorem unsat : Unsat cnf := by
  apply unsat_of_raw
  intro t ht
  have hs : TreeTrue t start := start_true (raw := raw) (h := {height}) (slots := {slots}) t ht
  exact final_false2 (s := start) (ps := proof) (h := {height}) t checked hs
#print axioms checked
#print axioms unsat
end {name}
'''
header='''namespace PeerLratFormatControls
open Snake9.LocalWindow
open Snake9.LratO5k (Tree TreeTrue andB unsat_of_raw)
open Snake9.PeerLratFast5000W18
open Snake9.PeerLratFast2_5000W18
'''
parts=[prefix,header]
parts.append(block('Variable4007',[[4007],[-4007]],[1,2],2,[(3,[],[FLAG+1,FLAG+2])],3))
parts.append(block('ClauseID70000',[[1],[-1]],[70000,70001],17,[(70002,[],[FLAG+70000,FLAG+70001])],70002))
long=list(range(1,301));clauses=[long]+[[-v] for v in long]
parts.append(block('LearnedClause300',clauses,list(range(1,302)),9,[(302,long,[FLAG+1]),(303,[],[FLAG+k for k in range(2,302)]+[302])],303))
sat_proof=pack([3,0,FLAG+1,FLAG+2,0]);bad_proof=pack([3,0,FLAG+999,0])
parts.append(f'''namespace RejectControls
def raw : List (List Nat) := [[2],[4]]
def cnf := raw.map (List.map decodeLit)
noncomputable def start : Tree := loadRaw (perf 2 0) raw [1,2]
noncomputable def falseProof : List Nat := [nat_lit {sat_proof}]
noncomputable def malformedProof : List Nat := [nat_lit {bad_proof}]
theorem false_unsat_rejected : check2 start (perf 2 0) falseProof = false := by decide +kernel
theorem missing_hint_rejected : check2 start (perf 2 0) malformedProof = false := by decide +kernel
theorem actual_sat_assignment : cnfTrue (fun _ => true) cnf = true := by decide +kernel
theorem not_unsat : Not (Unsat cnf) := by
  intro h
  have bad : (true : Bool) = false := actual_sat_assignment.symm.trans (h (fun _ => true))
  cases bad
#print axioms false_unsat_rejected
#print axioms missing_hint_rejected
#print axioms actual_sat_assignment
#print axioms not_unsat
end RejectControls
end PeerLratFormatControls
''')
text='\n\n'.join(parts);p=H/'PeerLratFormatControlsStandalone.lean';p.write_text(text,encoding='utf-8')
negative=text+'''\n/- EXPECTED FAILURE NEGATIVE CONTROL: a satisfiable CNF has no valid refutation. -/
theorem deliberately_invalid_LRAT_check :
  Snake9.PeerLratFast2_5000W18.check2
    PeerLratFormatControls.RejectControls.start
    (Snake9.PeerLratFast5000W18.perf 2 0)
    PeerLratFormatControls.RejectControls.falseProof = true := by
  decide +kernel
#print axioms deliberately_invalid_LRAT_check
'''
q=H/'PeerLratDeliberatelyInvalidStandalone.lean';q.write_text(negative,encoding='utf-8')
manifest={'status':'Prepared; online Lean checking not yet performed','positive_controls':['OFF5000 variable4007','clauseID70000 >65536','learned clause300 literals >255'],'rejection_controls':['missing hint','satisfiable formula false refutation'],'expected_failure_file':q.name,'files':{f.name:{'bytes':f.stat().st_size,'sha256':hashlib.sha256(f.read_bytes()).hexdigest()} for f in (p,q)}}
(H/'lrat_controls_preparation.json').write_text(json.dumps(manifest,indent=2));print(json.dumps(manifest,indent=2))
