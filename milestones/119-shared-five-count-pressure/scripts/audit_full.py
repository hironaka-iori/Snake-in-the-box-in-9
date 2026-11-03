"""Verify full-cube probe provenance, every cycle cut and complete positive paths."""
from pathlib import Path
from itertools import combinations
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted((H/'data/full-probes').glob('*.json')):
    d=json.loads(p.read_text());assert d['radius']==9
    assert sha(H/'scripts/probe_full.py')==d['script_sha256']
    for source,digest in d['source_files_sha256'].items():assert sha(R/source)==digest
    window=[0]
    for k in d['directions']:window.append(window[-1]^(1<<k))
    cuts=d['cycle_cuts']
    for cut in cuts:
        C=set(cut);assert len(C)==len(cut)>2 and all(0<=v<512 for v in C)
        adj={v:{v^(1<<k) for k in range(9)}&C for v in C}
        assert all(len(ns)==2 for ns in adj.values())
        seen={cut[0]};todo=list(seen)
        while todo:
            for w in adj[todo.pop()]-seen:seen.add(w);todo.append(w)
        assert seen==C
    row=dict(probe=p.relative_to(H).as_posix(),sha256=sha(p),status=d['status'],validated_cycle_cuts=len(cuts),seconds=d['solver_seconds'])
    if d['status']=='SAT_LOCAL_WITNESS':
        S=set(d['selected']);assert len(S)==len(d['selected']) and set(window)<=S
        assert all(0<=v<512 for v in S)
        adj={v:{v^(1<<k) for k in range(9)}&S for v in S}
        assert all(1<=len(ns)<=2 for ns in adj.values())
        ends=sorted(v for v in S if len(adj[v])==1);assert len(ends)==2
        order=[];v=ends[0]
        while True:
            order.append(v);n=adj[v]-set(order)
            if not n:break
            assert len(n)==1;v=n.pop()
        assert len(order)==len(S)
        for i,j in combinations(range(len(order)),2):assert ((order[i]^order[j]).bit_count()==1)==(j==i+1)
        if not any(order[i:i+7]==window for i in range(len(order)-6)):order.reverse()
        start=next(i for i in range(len(order)-6) if order[i:i+7]==window)
        counts=[]
        for i,c in enumerate(window[1:-1],1):
            used={c^window[i-1],c^window[i+1]}
            counts.append(sum(c^(1<<a)^(1<<b) not in S for a,b in combinations(range(9),2) if (1<<a) not in used and (1<<b) not in used))
        assert counts==d['census']['alpha'] and all(lo<=v<=hi for v,(lo,hi) in zip(counts,d['bounds']))
        assert sum(counts[i] for i in d['positions'])<=d['cap']
        assert all(not set(cut)<=S for cut in cuts)
        row.update(edges=len(order)-1,vertices=order,window_start=start,counts=counts,all_pairs_checked=len(order)*(len(order)-1)//2,endpoint_count=2)
    else:assert d['status'] in ['UNKNOWN','UNSAT_UNCERTIFIED'] and d['selected'] is None
    rows.append(row)
out=dict(status='PASS_FULL_Q9_PROBES_AND_COMPLETE_PATHS',probes=rows,script_sha256=sha(Path(__file__)),
    scope='Positive records independently verified as complete induced paths. UNKNOWN remains unresolved. No negative answer is certified by this audit; native contradiction replay is separate.')
p=H/'data/full-probe-audit.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
for r in rows:print(r['probe'],r['status'],'edges',r.get('edges'),'counts',r.get('counts'),'cuts',r['validated_cycle_cuts'])
