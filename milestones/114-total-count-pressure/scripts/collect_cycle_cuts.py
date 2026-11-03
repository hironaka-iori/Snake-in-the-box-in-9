"""Reuse only independently validated cycle exclusions contained in this local region."""
from pathlib import Path
from itertools import combinations
import hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
from gen_lean_sat import TaggedEncoding
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
probe=json.loads((HERE/'data/probes/012310-total18.json').read_text())
window=[0]
for d in probe['directions']:window.append(window[-1]^(1<<d))
enc=TaggedEncoding(window,[tuple(x) for x in probe['bounds']],radius=4)
lits=[]
for j in probe['positions']:
    i=j+1;v=window[i];used={v^window[i-1],v^window[i+1]}
    lits += [-enc.var[v^(1<<a)^(1<<b)] for a,b in combinations(range(9),2) if (1<<a) not in used and (1<<b) not in used]
lits.sort();enc.atmost(lits,probe['cap'],('unproved_sum',))
pool={};sources={};rejected=0
for milestone in ['110-exact-window-cells','111-critical-count-intervals','112-critical-sum-refinement','113-all-four-sum-pressure','114-total-count-pressure']:
    folder=ROOT/'milestones'/milestone/'data/probes'
    if not folder.exists():continue
    for path in sorted(folder.glob('*.json')):
        data=json.loads(path.read_text(encoding='utf-8-sig'))
        for row in data.get('cycle_cuts',[]):
            cut=tuple(sorted(row));S=set(cut)
            assert len(S)==len(cut) and len(S)>=4 and all(0<=v<512 for v in S)
            adj={v:{v^(1<<d) for d in range(9)}&S for v in S}
            assert all(len(ns)==2 for ns in adj.values())
            reached={cut[0]};todo=[cut[0]]
            while todo:
                v=todo.pop();new=adj[v]-reached;reached|=new;todo.extend(new)
            assert reached==S
            if not S<=set(enc.ball):rejected+=1;continue
            rel=path.relative_to(ROOT).as_posix();sources[rel]=sha(path)
            pool.setdefault(cut,[]).append(rel)
original={tuple(sorted(x)) for x in probe['cycle_cuts']}
assert original<=set(pool)
for cut in sorted(pool):enc.add([-enc.var[v] for v in cut],('cut',))
folder=HERE/'work/pooled-cuts';folder.mkdir(exist_ok=True)
cnf=folder/'full.cnf';assert not cnf.exists()
cnf.write_bytes((f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode())
out=dict(status='VALIDATED_CYCLE_CUT_POOL',source_files_sha256=sources,script_sha256=sha(Path(__file__)),
    window=window,directions=probe['directions'],bounds=probe['bounds'],positions=probe['positions'],cap=probe['cap'],
    cuts=[dict(vertices=list(c),sources=s) for c,s in sorted(pool.items())],original_cuts=len(original),
    additional_cuts=len(pool)-len(original),outside_region=rejected,variables=enc.nv,clauses=len(enc.clauses),
    cnf=cnf.relative_to(HERE).as_posix(),cnf_sha256=sha(cnf),
    scope='Every added set is directly checked to be a connected induced cube cycle wholly inside the current radius-four region. Such a set cannot be contained in an induced path. Native and Lean proof generation remain separate.')
target=HERE/'data/cycle-cut-pool.json';assert not target.exists()
target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('CUT_POOL',len(pool),'additional',out['additional_cuts'],'clauses',len(enc.clauses),flush=True)
