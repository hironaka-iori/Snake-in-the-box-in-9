"""Produce and independently replay a fresh LRAT certificate for one count case."""
from pathlib import Path
import hashlib,importlib.util,json,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod
for d in ['work','lean','data/meta','logs','build-isolated']:(HERE/d).mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
from gen_lean_sat import TaggedEncoding,code,write_module
import gen_lean_sat as satgen
from wincert import window_from_dirs,Encoding
probe=read(HERE/'data/plain-probes/edge3534483-plain.json')
assert probe['directions']==[0,1,2,3,4,0] and probe['counts']==[5,5,2,4,5]
assert probe['cycle_cuts']==[]
pins={}
for rel in ['milestones/10-window-aggregate/scripts/gen_lean_sat.py','milestones/10-window-aggregate/scripts/wincert.py',
 'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py',
 'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py']:
    p=ROOT/rel;pins[rel]=sha(p);dest=HERE/'upstream'/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
    if rel in probe['source_files_sha256']:assert pins[rel]==probe['source_files_sha256'][rel]
enc=TaggedEncoding(window_from_dirs(probe['directions']),[tuple(b) for b in probe['bounds']],radius=4)
reference=Encoding(enc.window,[tuple(b) for b in probe['bounds']],radius=4)
assert enc.clauses==reference.clauses and enc.nv==reference.nv
name='d012340_a5_5_2_4_5';mod='D012340A55245'
cnf=HERE/'work'/(name+'.cnf')
cnf.write_bytes((f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode('ascii'))
raw=HERE/'work/plain.raw.lrat';record=HERE/'data/plain-solver.json'
cadical=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
if not record.exists():
    assert not raw.exists()
    args=[str(cadical),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)]
    start=time.monotonic();proc=subprocess.run(args,capture_output=True,text=True,timeout=60)
    (HERE/'logs/plain-solver.stdout.txt').write_text(proc.stdout,encoding='utf-8')
    (HERE/'logs/plain-solver.stderr.txt').write_text(proc.stderr,encoding='utf-8')
    out=dict(command=args,solver_sha256=sha(cadical),cnf_sha256=sha(cnf),exit_code=proc.returncode,seconds=time.monotonic()-start,raw_sha256=sha(raw))
    record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
else:out=read(record)
assert out['exit_code']==20 and out['cnf_sha256']==sha(cnf) and out['raw_sha256']==sha(raw)
coregen=load(ROOT/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py','core110')
trimmed=HERE/'work'/(name+'.lrat')
nl,nh,ids=coregen.trim_lrat(str(raw),str(trimmed),len(enc.clauses))
# Independent elementary ordered RUP replay, without the exporter/checker's code.
database={i+1:set(c) for i,c in enumerate(enc.clauses)}
last=None
for line in trimmed.read_text().splitlines():
    row=list(map(int,line.split()));z=row.index(0,1);cid=row[0];clause=row[1:z];hints=row[z+1:-1]
    assert cid not in database and row[-1]==0 and all(h>0 for h in hints)
    truth={-lit for lit in clause};contradiction=any(-lit in truth for lit in truth)
    for h in hints:
        remaining=database[h]-{-lit for lit in truth}
        if not remaining:contradiction=True;break
        assert len(remaining)==1,(cid,h,'not unit')
        lit=next(iter(remaining));truth.add(lit)
    assert contradiction,(cid,'no contradiction')
    database[cid]=set(clause);last=clause
assert last==[]
meta=dict(module='LocalWindowCnf.'+mod,dirs=probe['directions'],syms=probe['counts'],window=enc.window,
 bounds=probe['bounds'],radius=4,cnf_clauses=len(enc.clauses),core_ids=ids)
(HERE/'data/meta'/(name+'.json')).write_text(json.dumps(meta,indent=2)+'\n',encoding='utf-8')
body=',\n  '.join(str([code(l) for l in enc.clauses[i-1]]) for i in ids)
src=f'''import LocalWindowDirModel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.{mod}
def window : List Nat := winOf {probe['directions']}
def bounds : List (Nat × Nat) := boundsOf {probe['counts']}
def raw : List (List Nat) := [
  {body}]
def cnf : List (List Int) := raw.map (·.map decodeLit)
end Snake9.LocalWindow.{mod}
'''
(HERE/'lean/LocalWindowCnf').mkdir(exist_ok=True)
(HERE/'lean/LocalWindowCnf'/(mod+'.lean')).write_text(src,encoding='utf-8')
satgen.LEAN=str(HERE/'lean')
write_module(name,mod,meta,enc,[enc.tags[i-1] for i in ids])
gen=load(ROOT/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py','lrat110')
gen.set_width(14,fast=True,off=4000);gen.DATA_DEF='noncomputable def'
stats=gen.export(name,str(HERE/'work'),3000,2,1,True,str(HERE/'lean'),str(HERE/'data/meta'))
assert all(sha(ROOT/p)==h for p,h in pins.items())
summary=dict(status='INDEPENDENT_RUP_PASS_LEAN_PENDING',variables=enc.nv,clauses=len(enc.clauses),core_clauses=len(ids),
 lemmas=nl,hints=nh,generation=stats,input_files_sha256=pins,cnf_sha256=sha(cnf),raw_sha256=sha(raw),lrat_sha256=sha(trimmed),
 script_sha256=sha(Path(__file__)),scope='Fresh full CNF, equivalent independent encoding, native LRAT and independent ordered RUP replay. Lean semantics and theorem checking pending.')
(HERE/'data/plain-generation.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print(json.dumps(summary,indent=2))
