"""Record elementary count and degree deductions for every critical window."""
from pathlib import Path
import collections,itertools,json,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
NB=[{x^(1<<d) for d in range(9)} for x in range(512)]
PAIRS=list(itertools.combinations(range(9),2))
def setup(edge):
    W=[0]
    for d in edge['directions']:W.append(W[-1]^(1<<d))
    constraints=[]
    for k,c in enumerate(edge['counts']):
        j=k+3;free=set(range(9))-{edge['directions'][j-1],edge['directions'][j]}
        K=sorted(W[j]^(1<<a)^(1<<b) for a,b in itertools.combinations(sorted(free),2))
        constraints.append(dict(position=j,corners=K,lo=c,hi=21 if c==6 else c))
    return W,constraints
def closure(W,constraints,branch=None,seed=None):
    S,D=(set(W),set()) if seed is None else (set(seed[0]),set(seed[1]))
    trace=[]
    if branch is not None:
        k,missing=branch;K=set(constraints[k]['corners'])
        S|=K-{missing};D.add(missing)
    for iteration in range(1025):
        if S&D:return dict(status='CONTRADICTION',reason=['conflict',min(S&D)],trace=trace)
        for v in sorted(S):
            if len(NB[v]&S)>2:return dict(status='CONTRADICTION',reason=['degree',v],trace=trace)
        crowded={v for v in range(512) if len(NB[v]&S)>2}-D
        if crowded:D|=crowded;trace.append(dict(rule='crowded',absent=sorted(crowded)))
        saturated=[v for v in sorted(S) if len(NB[v]&S)==2]
        fresh=set().union(*(NB[v]-S for v in saturated))-D if saturated else set()
        if fresh:D|=fresh;trace.append(dict(rule='saturated',absent=sorted(fresh)))
        changed=bool(crowded or fresh)
        for k,c in enumerate(constraints):
            K=set(c['corners']);absent=K&D;selected=K&S
            if len(absent)>c['hi']:return dict(status='CONTRADICTION',reason=['count_upper',k],trace=trace)
            if len(selected)>21-c['lo']:return dict(status='CONTRADICTION',reason=['count_lower',k],trace=trace)
            if len(absent)==c['hi']:
                fresh=K-D-S
                if fresh:S|=fresh;trace.append(dict(rule='count_upper',constraint=k,selected=sorted(fresh)));changed=True
            if len(selected)==21-c['lo']:
                fresh=K-S-D
                if fresh:D|=fresh;trace.append(dict(rule='count_lower',constraint=k,absent=sorted(fresh)));changed=True
        if not changed:break
    else:raise AssertionError('No fixed point')
    assert not(S&D)
    lower=0
    for c in W[4:9]:
        for q in NB[c]:
            empty=sum({q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}<=D for a,b in PAIRS)
            degree=len(NB[q]-D);assert degree>0
            lower+=12*empty//degree
    return dict(status='CLOSED',selected=sorted(S),absent=sorted(D),lower=lower,trace=trace)
def main():
    edges=json.loads((ROOT/'milestones/61-critical-family-share/data/critical-edges.json').read_text())
    results=[];start=time.monotonic()
    (HERE/'data/cases').mkdir(exist_ok=True)
    for i,e in enumerate(edges):
        W,C=setup(e);trials=[]
        sites=[k for k,c in enumerate(C) if c['lo']==c['hi']==1]
        if not sites:sites=[None]
        for k in sites:
            branches=[]
            for missing in C[k]['corners'] if k is not None else [None]:
                r=closure(W,C,(k,missing) if k is not None else None)
                branches.append(dict(missing=missing,**r))
            survivors=[b for b in branches if b['status']=='CLOSED']
            trials.append(dict(site=k,branches=branches,lower=min(b['lower'] for b in survivors) if survivors else None))
        selected=next((j for j,t in enumerate(trials) if t['lower'] is None),None)
        if selected is None:selected=max(range(len(trials)),key=lambda j:trials[j]['lower'])
        chosen=trials[selected];status='EXCLUDED_CANDIDATE' if chosen['lower'] is None else 'SHARE_CANDIDATE'
        payload=dict(edge=i,directions=e['directions'],counts=e['counts'],vertices=W,constraints=C,trials=trials,chosen=selected,status=status,
                     lower=chosen['lower'],old_lower=e['share_lower'],scope='Recorded deterministic deductions; Lean checking pending.')
        (HERE/f'data/cases/e{i:02d}.json').write_text(json.dumps(payload,indent=2)+'\n')
        results.append({k:v for k,v in payload.items() if k not in ['trials','constraints','vertices','scope']})
    summary=dict(results=results,status_counts=dict(collections.Counter(r['status'] for r in results)),seconds=time.monotonic()-start,
                 scope='All results are candidates until the count branch and propagation deductions have passed Lean checks.')
    (HERE/'data/summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(summary['status_counts'],'seconds',summary['seconds'])
    print('Remaining bounds',[(r['edge'],r['old_lower'],r['lower']) for r in results if r['lower'] is not None])
if __name__=='__main__':main()
