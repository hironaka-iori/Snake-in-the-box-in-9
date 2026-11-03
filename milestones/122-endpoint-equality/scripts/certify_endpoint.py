"""Export endpoint-clause refutations with separate checked clause semantics."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
import gen_lean_sat as satgen
from wincert import window_from_dirs
def load(path,name):
    sp=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m
ap=argparse.ArgumentParser();ap.add_argument('probe');ap.add_argument('name');ap.add_argument('module');args=ap.parse_args();name=args.name;mod=args.module
probe=ROOT/'milestones/121-replacement-window-pressure'/args.probe
case=read(probe);assert case['status']=='UNSAT_UNCERTIFIED'
assert not case['cycle_cuts'] and case['radius']==9
enc=satgen.TaggedEncoding(window_from_dirs(case['directions']),[tuple(b) for b in case['bounds']],radius=9)
common=case['common_sphere']
assert common==[v for v in range(512) if all((v^c).bit_count()==2 for c in [3,6])]
assert all(enc.meaning[513+v]==('e',v) for v in range(512))
enc.add([513+v for v in range(512) if v not in common],('endpointOutsideCommon2',))
for cut in case['cycle_cuts']:
    assert satgen.is_cycle_set(cut) and all(v in enc.var for v in cut)
    enc.add([-enc.var[v] for v in cut],('cut',))
work=HERE/'work'/name;work.mkdir(exist_ok=True)
cnf=work/(name+'.cnf');cnf.write_bytes((f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode())
raw=work/'raw.lrat';rp=HERE/'data'/(name+'-solver.json')
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
command=[str(exe),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)];start=time.monotonic()
out=dict(command=command,solver_sha256=sha(exe),cnf_sha256=sha(cnf),timeout_seconds=60)
if rp.exists():
    out=read(rp)
    assert out['cnf_sha256']==sha(cnf) and out['raw_sha256']==sha(raw)
else:
    try:
        p=subprocess.run(command,capture_output=True,text=True,timeout=60)
        (HERE/'logs'/(name+'-solver.stdout.txt')).write_text(p.stdout);(HERE/'logs'/(name+'-solver.stderr.txt')).write_text(p.stderr)
        out.update(status='NATIVE_UNSAT_LEAN_PENDING' if p.returncode==20 and 's UNSATISFIABLE' in p.stdout else 'FAILED',exit_code=p.returncode,seconds=time.monotonic()-start)
    except subprocess.TimeoutExpired as exc:out.update(status='TIMEOUT',seconds=time.monotonic()-start)
    finally:
        if raw.exists():out['raw_sha256']=sha(raw)
        rp.write_text(json.dumps(out,indent=2)+'\n')
assert out['status']=='NATIVE_UNSAT_LEAN_PENDING',out
old=ROOT/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts'
gen=load(old/'gen_lean_core.py','gcore122');trim=work/(name+'.lrat')
nl,nh,ids=gen.trim_lrat(str(raw),str(trim),len(enc.clauses))
assert enc.nv<2400 and ids[-1]==len(enc.clauses)
prior=read(ROOT/'milestones/121-replacement-window-pressure/data/endpoint-probe-audit.json')
expected=next(r for r in prior['probes'] if r['probe']==args.probe)
assert sha(cnf)==expected['cnf_sha256']
meta=dict(module='LocalWindowCnf.'+mod,dirs=case['directions'],window=enc.window,bounds=case['bounds'],radius=9,cnf_clauses=len(enc.clauses),core_ids=ids)
(HERE/'data/meta').mkdir(exist_ok=True);(HERE/'data/meta'/(name+'.json')).write_text(json.dumps(meta,indent=2)+'\n')
generated=HERE/'generated';(generated/'LocalWindowCnf').mkdir(parents=True,exist_ok=True)
body=',\n  '.join(str([satgen.code(v) for v in enc.clauses[i-1]]) for i in ids[:-1])
src=f'''import LocalWindowDirModel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.{mod}
def window : List Nat := winOf {case['directions']}
def bounds : List (Nat × Nat) := {[tuple(b) for b in case['bounds']]}
def baseRaw : List (List Nat) := [
  {body}]
def common : List Nat := {common}
def endpointRaw : List Nat := {[satgen.code(v) for v in enc.clauses[-1]]}
def raw : List (List Nat) := baseRaw ++ [endpointRaw]
def cnf : List (List Int) := raw.map (·.map decodeLit)
end Snake9.LocalWindow.{mod}
'''
(generated/'LocalWindowCnf'/(mod+'.lean')).write_text(src,encoding='utf-8')
satgen.LEAN=str(generated);satgen.write_module(name,mod,meta,enc,[enc.tags[i-1] for i in ids[:-1]])
sp=generated/'LocalWindowSat'/(mod+'.lean');st=sp.read_text()
st=st.replace('import LocalWindowTags','import EndpointClause122')
st=st[:st.index('theorem check :')]+f'''theorem check : checkAll meaning ctrs window bounds tags baseRaw = true := by decide +kernel

theorem check_endpoint : endpointRaw.all (posE meaning) = true := by decide +kernel

theorem coverage : endpointRaw.map (vl meaning) =
    (List.range 512).filter (fun v => !common.contains v) := by decide +kernel

theorem sat : ∀ S E : Nat → Bool,
    Axioms S E window (centresOf window bounds) →
    (∃ v, v < 512 ∧ E v = true ∧ v ∉ common) → ∃ τ, cnfTrue τ cnf = true := by
  intro S E ax hbad
  obtain ⟨v, hv, hE, hc⟩ := hbad
  have hm : v ∈ endpointRaw.map (vl meaning) := by
    rw [coverage]
    simp [hv, hc]
  obtain ⟨a, ha, hav⟩ := List.mem_map.mp hm
  refine ⟨tau S E meaning ctrs, ?_⟩
  exact Snake9.EndpointClause122.sat_append S E meaning ctrs window bounds tags
    baseRaw endpointRaw check check_endpoint ⟨a, ha, by simpa only [hav] using hE⟩ ax

end Snake9.LocalWindow.{mod}

#print axioms Snake9.LocalWindow.{mod}.sat
'''
sp.write_text(st,encoding='utf-8')
lr=load(old/'gen_lean_lrat.py','glrat122');lr.set_width(13,fast=True,off=2400);lr.LIT_FUEL=1023;lr.CHECKER_IMPORT='import LratFastEndpoint122';lr.CHECKER_OPEN='open Snake9.LratFastEndpoint122\nopen Snake9.Lrat (Tree TreeTrue andB)';lr.DATA_DEF='noncomputable def';lr.GROUPED=True
stats=lr.export(name,str(work),6000,6,6,True,str(generated),str(HERE/'data/meta'))
mods=['LocalWindowCnf.'+mod,'LocalWindowSat.'+mod]
mods+=['LocalWindowUnsat.'+mod+'.Data'+str(i) for i in range(stats['check_modules']+1)]
mods+=['LocalWindowUnsat.'+mod+'.Check'+str(i+1) for i in range(stats['check_modules'])]
mods+=['LocalWindowUnsat.'+mod];ports=[]
for module in mods:
    p=generated/(module.replace('.','/')+'.lean');txt=p.read_text()
    dest=HERE/'lean/Recovered122G'/p.relative_to(generated);dest.parent.mkdir(parents=True,exist_ok=True)
    changed=re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.'+mod+r'(?:\.[A-Za-z0-9]+)?)$',r'import Recovered122G.\1',txt,flags=re.M)
    dest.write_text(changed,encoding='utf-8');assert re.sub(r'^import Recovered122G\.',r'import ',changed,flags=re.M)==txt
    ports.append(dict(original=p.relative_to(HERE).as_posix(),source_sha256=sha(p),isolated=dest.relative_to(HERE).as_posix(),isolated_sha256=sha(dest)))
pins={p.relative_to(ROOT).as_posix():sha(p) for p in [old/'gen_lean_core.py',old/'gen_lean_lrat.py',ROOT/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',ROOT/'milestones/10-window-aggregate/scripts/wincert.py']}
out=dict(status='GENERATED_NOT_CHECKED',modules=['Recovered122G.'+m for m in mods],ports=ports,generation=stats,
    core_clauses=len(ids),variables=enc.nv,clauses=len(enc.clauses),lemmas=nl,hints=nh,lrat_sha256=sha(trim),cnf_sha256=sha(cnf),
    probe=str(probe.relative_to(ROOT)),probe_sha256=sha(probe),common_sphere=common,endpoint_clause_size=498,cycle_cuts=case['cycle_cuts'],source_files_sha256=pins,script_sha256=sha(Path(__file__)))
(HERE/'data'/(name+'-plan.json')).write_text(json.dumps(out,indent=2)+'\n')
print('Generated',len(mods),'modules,',len(ids),'core clauses,',nl,'deductions,',nh,'hints',flush=True)
