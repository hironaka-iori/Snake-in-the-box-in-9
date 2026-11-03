"""Independent count-window geometry, cut and provenance audit."""
from pathlib import Path
from itertools import combinations
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted((H/'data/probes').glob('*.json')):
    d=read(p);assert d['sum_cap'] is None and not d['sum_counter_added']
    assert sha(H/'scripts/probe_window.py')==d['script_sha256']
    for path,digest in d['source_files_sha256'].items():assert sha(R/path)==digest
    win=[0]
    for k in d['directions']:win.append(win[-1]^(1<<k))
    assert win==d['window'] and len(d['bounds'])==len(win)-2
    B={v for v in range(512) if min((v^c).bit_count() for c in win[1:-1])<=d['radius']}
    assert len(B)==d['ball_vertices']
    for cut in d['cycle_cuts']:
        C=set(cut);assert len(C)==len(cut)>2 and C<=B
        adj={v:{v^(1<<k) for k in range(9)}&C for v in C};assert all(len(x)==2 for x in adj.values())
        seen={cut[0]};todo=list(seen)
        while todo:
            for v in adj[todo.pop()]-seen:seen.add(v);todo.append(v)
        assert seen==C
    row=dict(probe=p.relative_to(H).as_posix(),sha256=sha(p),status=d['status'],radius=d['radius'],cuts=len(d['cycle_cuts']),seconds=d['solver_seconds'])
    if d['selected'] is not None:
        S=set(d['selected']);assert len(S)==len(d['selected']) and S<=B and set(win)<=S
        adj={v:{v^(1<<k) for k in range(9)}&S for v in S};assert all(len(x)<=2 for x in adj.values())
        interior={v for v in S if all(v^(1<<k) in B for k in range(9))}
        assert all(len(adj[v])>=1 for v in interior)
        ends={v for v in interior if len(adj[v])==1};assert len(ends)<=2
        left=set(S);components=[]
        while left:
            C={left.pop()};todo=list(C)
            while todo:
                new=adj[todo.pop()]&left;left-=new;C|=new;todo.extend(new)
            assert sum(len(adj[v]) for v in C)//2==len(C)-1
            components.append(sorted(C))
        counts=[]
        for i,c in enumerate(win[1:-1],1):
            used={c^win[i-1],c^win[i+1]}
            counts.append(sum(c^(1<<a)^(1<<b) not in S for a,b in combinations(range(9),2) if (1<<a) not in used and (1<<b) not in used))
        assert counts==d['census']['alpha'] and all(lo<=v<=hi for v,(lo,hi) in zip(counts,d['bounds']))
        assert all(not set(cut)<=S for cut in d['cycle_cuts'])
        if d['radius']==9:assert len(components)==1 and len(ends)==2
        row.update(counts=counts,selected=len(S),components=[len(c) for c in components],interior_endpoints=len(ends),complete_snake=d['radius']==9)
    else:assert d['status'] in ['UNKNOWN','UNSAT_UNCERTIFIED']
    rows.append(row)
out=dict(status='PASS_WINDOW_PROVENANCE_CUTS_AND_POSITIVE_GEOMETRY',probes=rows,script_sha256=sha(Path(__file__)),scope='Positive geometry and all retained cuts independently checked. Native UNSAT statuses are not certified by this probe audit; the selected outer3 proof has separate native and Lean evidence. UNKNOWN remains unresolved.')
p=H/'data/probe-audit.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
for r in rows:print(r['probe'],r['status'],r.get('counts'),r.get('components'))
