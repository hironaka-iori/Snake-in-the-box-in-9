from pathlib import Path
import json,hashlib,collections,itertools
H=Path('milestones/217-long-parent-search'); p=Path('outputs/snake8_witness.json'); P=json.loads(p.read_bytes())['vertex_sequence']; reports=[]
for root in [P[0],P[-1]]:
    V=sorted(set(range(256))-(set(P)-{root})); S=set(V); N={v:[v^(1<<i) for i in range(8) if v^(1<<i) in S] for v in V}
    seen=set(); comps=[]
    for v in V:
        if v in seen:continue
        seen.add(v); todo=[v]; comp=[]
        while todo:
            u=todo.pop();comp.append(u)
            for w in N[u]:
                if w not in seen: seen.add(w);todo.append(w)
        comps.append(sorted(comp))
    cuts={}
    for cut in V:
        seen={cut}; parts=[]
        for v in V:
            if v in seen:continue
            seen.add(v); todo=[v]; part=[]
            while todo:
                u=todo.pop();part.append(u)
                for w in N[u]:
                    if w not in seen:seen.add(w);todo.append(w)
            parts.append(sorted(part))
        if len(parts)>len(comps):cuts[str(cut)]=parts
    twins=collections.defaultdict(list)
    for v in V: twins[tuple(sorted(N[v]))].append(v)
    twins=[x for x in twins.values() if len(x)>1]
    squares=set(); sixes=set()
    for a,b in itertools.combinations(range(8),2):
        mask=(1<<a)|(1<<b)
        for base in range(256):
            if base&mask:continue
            C=tuple(sorted([base,base^(1<<a),base^(1<<b),base^mask]))
            if set(C)<=S:squares.add(C)
    for dims in itertools.combinations(range(8),3):
        mask=sum(1<<d for d in dims)
        for base in range(256):
            if base&mask:continue
            cube={base^sum((1<<d) for j,d in enumerate(dims) if t&(1<<j)) for t in range(8)}
            for u in sorted(cube):
                v=u^mask
                if u>=v:continue
                C=tuple(sorted(cube-{u,v}))
                if set(C)<=S:sixes.add(C)
    reports.append({'root':root,'allowed_vertices':V,'edges':sum(map(len,N.values()))//2,'even':sum(v.bit_count()%2==0 for v in V),'odd':sum(v.bit_count()%2==1 for v in V),'degree_counts':dict(sorted(collections.Counter(map(len,N.values())).items())),'components':comps,'articulation_deletions':cuts,'equal_neighbourhood_classes':twins,'root_neighbours':N[root],'coordinate_squares':sorted(squares),'three_cube_induced_six_cycles':sorted(sixes)})
out={'source':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'scope':'Finite graph analysis only; no path search or software tests.','reports':reports}
(H/'data/complement-graph.json').write_text(json.dumps(out,indent=2)+'\n')
for r in reports:print(json.dumps({k:v for k,v in r.items() if k not in ['allowed_vertices','components','coordinate_squares','three_cube_induced_six_cycles']})); print('components',[len(c) for c in r['components']], 'squares',len(r['coordinate_squares']),'three-cube six-cycles',len(r['three_cube_induced_six_cycles']))
