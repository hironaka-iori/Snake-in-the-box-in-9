"""Untrusted LRAT core trimming adapted from completed KEEP=112 pipeline."""
def trim(data,proofpath):
    n=len(data['clauses']);steps={}
    with proofpath.open(encoding='utf-8') as f:
        for line in f:
            fields=line.split()
            if not fields or fields[1]=='d':continue
            a=list(map(int,fields));z=a.index(0)
            steps[a[0]]=(a[1:z],a[z+1:-1])
    assert steps and not steps[max(steps)][0]
    raw={i:c for i,c in enumerate(data['clauses'],1)}
    raw.update({i:c for i,(c,_) in steps.items()})
    for ident,(target,hints) in list(steps.items()):
        assigned={abs(v):(v<0,None) for v in target};parents={};final=None
        for hint in hints:
            assert hint>0, 'Non-RUP hint'
            clause=raw[hint]
            assert not any(abs(v) in assigned and assigned[abs(v)][0]==(v>0) for v in clause)
            unknown=[v for v in clause if abs(v) not in assigned]
            assert len(unknown)<=1
            parents[hint]={assigned[abs(v)][1] for v in clause if abs(v) in assigned}-{None}
            if not unknown:final=hint;break
            v=unknown[0];assigned[abs(v)]=(v>0,hint)
        assert final is not None
        used=set();todo=[final]
        while todo:
            h=todo.pop()
            if h in used:continue
            used.add(h);todo.extend(parents[h])
        steps[ident]=(target,[h for h in hints if h in used])
    needed={max(steps)};todo=list(needed)
    while todo:
        k=todo.pop()
        if k<=n:continue
        for h in steps[k][1]:
            if h not in needed:needed.add(h);todo.append(h)
    original=sorted(k for k in needed if k<=n);derived=sorted(k for k in needed if k>n)
    ids={k:i+1 for i,k in enumerate(original+derived)}
    return dict(original_clause_indices=original,clauses=[data['clauses'][k-1] for k in original],
        reasons=[data['reasons'][k-1] for k in original],
        proof=[(ids[k],steps[k][0],[ids[h] for h in steps[k][1]]) for k in derived],
        scope='Untrusted trimmed Boolean certificate; kernel and geometry checks required.')
