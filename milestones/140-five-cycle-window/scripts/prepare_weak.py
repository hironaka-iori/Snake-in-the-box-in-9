"""Prepare a weaker semantic interpretation of the same checked CNF.

No solver, Lean process, or modification of the frozen exact export occurs.
"""
from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parents[1]
R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('x',encoding='utf-8',newline='\n') as f:f.write(value)

def main():
    plan=read(H/'data/proof-plan-base.json')
    sem=read(H/'data/selected-core-semantics-base.json')
    enc=read(H/'work/short/encoding.json')
    audit=read(H/'data/independent-semantics.json')
    assert audit['status']=='PASS_INDEPENDENT_ENCODING_AND_CORE_AUDIT'
    assert audit['unused_counter_indices']==[4,8]
    assert audit['unused_counter_registers_absent_from_core_and_proof']
    for a in plan['artifacts']:assert sha(H/a['path'])==a['sha256'],a['path']
    for p,digest in plan['source_files_sha256'].items():assert sha(R/p)==digest,p
    assert sha(H/'data/selected-core-semantics-base.json')==plan['semantic_data_sha256']
    assert sem['directions']==[0,1,2,0,3,2]
    assert sem['bounds']==[[3,3],[5,5],[4,4],[5,5],[3,3]]
    assert len(sem['counters'])==11
    register_vars={int(v) for v,m in sem['meaning'].items() if m[0]=='r' and m[1] in [4,8]}
    core_vars={abs(x) for c in sem['renamed_signed_raw'] for x in c}
    assert not register_vars&core_vars
    assert not any(t[0] in ['first','zero','mono','step','over'] and t[1] in [4,8] for t in sem['tags'])
    assert sem['counters'][4][2]==['lo',1] and sem['counters'][8][2]==['lo',3]
    # A literal of a used counter must not acquire a changed register value.
    used={t[1] for t in sem['tags'] if t[0] in ['first','zero','mono','step','over']}
    assert not any(abs(x) in register_vars for i in used for x in sem['counters'][i][0])
    weakbounds=[[3,3],[0,5],[4,4],[0,5],[3,3]]
    weakctrs=[c if i not in [4,8] else [[],2,['ends']] for i,c in enumerate(sem['counters'])]
    # Check every counter's elementary geometric condition against new bounds.
    meanings={int(v):m for v,m in sem['meaning'].items()}
    for lits,k,kind in weakctrs:
        if kind[0]=='ends':
            assert k==2 and all(x>0 and meanings[x][0]=='e' for x in lits)
            assert [meanings[x][1] for x in lits]==sorted(set(meanings[x][1] for x in lits))
        else:
            ci=kind[1];c=sem['window'][ci+1]
            dirs={(c^sem['window'][ci]).bit_length()-1,(c^sem['window'][ci+2]).bit_length()-1}
            corners=[c^(1<<a)^(1<<b) for a in range(9) for b in range(a+1,9) if a not in dirs and b not in dirs]
            assert len(corners)==21
            assert all(meanings[abs(x)][0]=='p' for x in lits)
            assert [meanings[abs(x)][1] for x in lits]==corners
            if kind[0]=='hi':assert all(x<0 for x in lits) and k==weakbounds[ci][1]
            else:assert kind[0]=='lo' and all(x>0 for x in lits) and k+weakbounds[ci][0]==21
    src='''import LocalWindowSat.CycleBase140

namespace Snake9.Weak140
open Snake9.LocalWindow Snake9.LocalWindow.Tags
open Snake9.LocalWindow.CycleBase140 (window meaning tags raw cnf)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def bounds : List (Nat × Nat) := [(3,3),(0,5),(4,4),(0,5),(3,3)]

def ctrs : List Ctr :=
  (Snake9.LocalWindow.CycleBase140.ctrs.set 4 dfltCtr).set 8 dfltCtr

theorem check : checkAll meaning ctrs window bounds tags raw = true := by
  decide +kernel

theorem sat : ∀ S E : Nat → Bool,
    Axioms S E window (centresOf window bounds) → ∃ τ, cnfTrue τ cnf = true :=
  fun S E h => ⟨tau S E meaning ctrs, sound meaning ctrs window bounds tags raw check S E h⟩

#print axioms check
#print axioms sat
end Snake9.Weak140
'''
    template=(H/'scripts/actual-wrapper.lean.txt').read_text(encoding='utf-8')
    canonical='theorem actual_canonical_frame'+template.split('theorem actual_canonical_frame',1)[1].split('#print axioms actual_canonical_frame',1)[0]
    bridge='theorem actual_refuted'+template.split('theorem actual_refuted',1)[1].split('#print axioms refuted',1)[0]
    wrapper='''import Weak140Semantics
import LocalWindowUnsat.CycleBase140
import DirectionWindowBridge
import Mathlib.Tactic

namespace Snake9.Weak140
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.LocalWindow.CycleBase140 (window)
set_option maxHeartbeats 2000000

'''+canonical+'''
#print axioms actual_canonical_frame

theorem refuted : Refuted window bounds :=
  Tags.refuted_of_sat sat Snake9.LocalWindow.CycleBase140.unsat

'''+bridge+'''
#print axioms refuted
#print axioms actual_refuted

theorem actual_weak_counts {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (h1 : coreAlpha p (r+1) = 3)
    (h2 : coreAlpha p (r+2) ≤ 5)
    (h3 : coreAlpha p (r+3) = 4)
    (h4 : coreAlpha p (r+4) ≤ 5)
    (h5 : coreAlpha p (r+5) = 3) : False := by
  apply actual_refuted p r hr hshape
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp_all [bounds, Nat.add_assoc]

theorem actual_one_count_ge_six {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (h1 : coreAlpha p (r+1) = 3)
    (h3 : coreAlpha p (r+3) = 4)
    (h5 : coreAlpha p (r+5) = 3) :
    6 ≤ coreAlpha p (r+2) ∨ 6 ≤ coreAlpha p (r+4) := by
  by_contra h
  push_neg at h
  exact actual_weak_counts p r hr hshape h1 (by omega) h3 (by omega) h5

#print axioms actual_weak_counts
#print axioms actual_one_count_ge_six
end Snake9.Weak140
'''
    for text in [src,wrapper]:assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text)
    outputs=[H/'lean/Weak140Semantics.lean',H/'lean/Weak140Actual.lean']
    inputs=[Path(__file__),H/'data/proof-plan-base.json',H/'data/selected-core-semantics-base.json',
        H/'data/independent-semantics.json',H/'scripts/actual-wrapper.lean.txt',
        H/'lean/LocalWindowCnf/CycleBase140.lean',H/'lean/LocalWindowSat/CycleBase140.lean',
        H/'lean/LocalWindowUnsat/CycleBase140.lean',R/'work/final_lean/LocalWindowTags.lean']
    pins={p.relative_to(R).as_posix():sha(p) for p in inputs}
    for p,text in zip(outputs,[src,wrapper]):write(p,text)
    for p,d in pins.items():assert sha(R/p)==d
    receipt=dict(status='SOURCE_PREPARED_LEAN_PENDING',module_order=['Weak140Semantics','Weak140Actual'],
        final_theorem='Snake9.Weak140.actual_one_count_ge_six',source_files_sha256=pins,
        outputs={p.relative_to(H).as_posix():sha(p) for p in outputs},expected_axiom_reports=[2,5],
        unchanged_cnf_module='LocalWindowCnf.CycleBase140',unchanged_unsat_module='LocalWindowUnsat.CycleBase140',
        weak_bounds=weakbounds,neutralized_counter_indices=[4,8],used_counter_indices=sorted(used),
        unused_registers=len(register_vars),unused_registers_absent_from_core=True,
        unused_registers_absent_from_used_counter_literals=True,elementary_counter_conditions_checked=True,
        scope='Source preparation only. Generic checkAll and actual-snake consequences await Lean. The original exact source and proof plan are unchanged; no solver or Lean ran.')
    write(H/'audit/weak-preparation.json',json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
