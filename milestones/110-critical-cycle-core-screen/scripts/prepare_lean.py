"""Renumber proof variables, export isolated Lean modules, and pin their environment."""
from pathlib import Path
import importlib.util,json,re,hashlib,sys,copy
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def load(path,name):
    sp=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
import gen_lean_sat as satgen
from wincert import window_from_dirs
name='d012340_a5_5_2_4_5';mod='D012340A55245'
meta=read(HERE/'data/meta'/(name+'.json'));ids=meta['core_ids']
enc=satgen.TaggedEncoding(meta['window'],[tuple(b) for b in meta['bounds']],radius=4)
active=sorted({abs(v) for i in ids for v in enc.clauses[i-1]})
order=active+sorted(set(range(1,enc.nv+1))-set(active));ren={v:i+1 for i,v in enumerate(order)}
assert len(active)<2400 and len(set(ren.values()))==enc.nv
def lit(v):return ren[abs(v)]*(1 if v>0 else -1)
enc.clauses=[[lit(v) for v in c] for c in enc.clauses]
enc.meaning={ren[v]:meaning for v,meaning in enc.meaning.items()}
enc.var={v:ren[x] for v,x in enc.var.items()}
enc.ctrs=[([lit(v) for v in lits],k,kind) for lits,k,kind in enc.ctrs]
work=HERE/'work/renumbered';work.mkdir(exist_ok=True)
(work/(name+'.cnf')).write_bytes((f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode())
original=HERE/'work/plain-core-s1.trim.lrat';ncore=len(ids);nfull=len(enc.clauses)
def cid(i):return ids[i-1] if i<=ncore else nfull+i-ncore
with (work/(name+'.lrat')).open('w',encoding='ascii',newline='\n') as out:
    for line in original.read_text().splitlines():
        row=list(map(int,line.split()));z=row.index(0,1)
        mapped=[cid(row[0]),*map(lit,row[1:z]),0,*map(cid,row[z+1:-1]),0]
        out.write(' '.join(map(str,mapped))+'\n')
outroot=HERE/'generated-remapped';(outroot/'LocalWindowCnf').mkdir(parents=True,exist_ok=True)
body=',\n  '.join(str([satgen.code(v) for v in enc.clauses[i-1]]) for i in ids)
src=f'''import LocalWindowDirModel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.{mod}
def window : List Nat := winOf {meta['dirs']}
def bounds : List (Nat × Nat) := boundsOf {meta['syms']}
def raw : List (List Nat) := [
  {body}]
def cnf : List (List Int) := raw.map (·.map decodeLit)
end Snake9.LocalWindow.{mod}
'''
(outroot/'LocalWindowCnf'/(mod+'.lean')).write_text(src,encoding='utf-8')
satgen.LEAN=str(outroot);satgen.write_module(name,mod,meta,enc,[enc.tags[i-1] for i in ids])
gen=load(ROOT/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py','g110')
gen.set_width(13,fast=True,off=2400);gen.DATA_DEF='noncomputable def'
stats=gen.export(name,str(work),6000,2,1,True,str(outroot),str(HERE/'data/meta'))
mods=['LocalWindowCnf.'+mod,'LocalWindowSat.'+mod]
mods+=['LocalWindowUnsat.'+mod+'.Data'+str(i) for i in range(stats['segments']+1)]
mods+=['LocalWindowUnsat.'+mod+'.Check'+str(i+1) for i in range(stats['check_modules'])]
mods+=['LocalWindowUnsat.'+mod]
ports=[]
for module in mods:
    path=outroot/(module.replace('.','/')+'.lean');txt=path.read_text()
    dest=HERE/'lean/Recovered110'/path.relative_to(outroot);dest.parent.mkdir(parents=True,exist_ok=True)
    changed=re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.'+mod+r'(?:\.[A-Za-z0-9]+)?)$',r'import Recovered110.\1',txt,flags=re.M)
    dest.write_text(changed,encoding='utf-8')
    assert re.sub(r'^import Recovered110\.',r'import ',changed,flags=re.M)==txt
    ports.append(dict(original=path.relative_to(HERE).as_posix(),sha256=sha(path),isolated=dest.relative_to(HERE).as_posix(),isolated_sha256=sha(dest)))
old=ROOT/'milestones/109-relaxed-graph-test';environment=read(old/'data/environment-isolated.json')
environment=dict(status='PINNED_NEW_COUNT_EXCLUSION_ENVIRONMENT',paths=[str(HERE/'build-isolated')]+environment['paths'],
 receipts={**environment['receipts'],(old/'data/environment-isolated.json').relative_to(ROOT).as_posix():sha(old/'data/environment-isolated.json')},
 scope='Reuses the verified prior overlay without copying or changing it. New modules use Recovered110 imports.')
ep=HERE/'data/environment-isolated.json';assert not ep.exists();ep.write_text(json.dumps(environment,indent=2)+'\n')
(HERE/'scripts/check_isolated.py').write_bytes((old/'scripts/check_isolated.py').read_bytes())
summary=dict(status='GENERATED_NOT_CHECKED',active_variables=len(active),all_variables=enc.nv,renumbering=[[v,ren[v]] for v in order],
 generation=stats,modules=['Recovered110.'+m for m in mods],ports=ports,original_core_lrat_sha256=sha(original),
 remapped_cnf_sha256=sha(work/(name+'.cnf')),remapped_lrat_sha256=sha(work/(name+'.lrat')),
 script_sha256=sha(Path(__file__)))
(HERE/'data/isolated-plan.json').write_text(json.dumps(summary,indent=2)+'\n')
print('Prepared',len(mods),'modules;',stats['hints'],'hints;',len(active),'active variables.')
