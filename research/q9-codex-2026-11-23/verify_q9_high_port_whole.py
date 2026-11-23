"""Independently reconstruct whole-facet integer duals and combine both endpoint-colour searches."""
import gzip,json
from pathlib import Path
from collections import Counter,defaultdict
from itertools import combinations
from verify_q9_high_port_completions import allowed
from verify_q9_intact98_all_crossings import check
from search_q9_high_port_dual_completion import verify as check_path

def value(c,fixed,D,goal,ep):
    scale,alpha,beta=c['scale'],c['end'],c['balance']
    check(all(type(a) is int for a in (scale,alpha,beta)) and scale>0,'noninteger weight')
    masks=[sum(1<<j for j in ax) for ax in c['axes']]
    w={(m,v,z):y for m,v,z,y in c['weights']}
    check(len(w)==len(c['weights']) and all(type(y) is int for y in w.values()),'invalid weights')
    delta=0 if goal%2 else 1-2*ep
    total=2*alpha+delta*beta
    valid={}
    for v in D:
        dirs=[1<<i for i in range(9) if v^(1<<i) in D]
        must=sum(d for d in dirs if v^d in fixed)
        zs=[a|b for a,b in combinations(dirs,2)]
        if goal%2 or v.bit_count()%2==ep:zs+=dirs
        zs=[z for z in zs if z&must==must]
        scores=[] if v in fixed else [0]
        for z in zs:scores.append(scale-(1-2*(v.bit_count()%2))*beta-(alpha if z.bit_count()==1 else 0)+sum(w.get((m,v,z&m),0) for m in masks))
        check(scores,'no local option')
        total+=max(scores)
        for m in masks:valid[v,m]={z&m for z in zs}
    for m in masks:
        groups=defaultdict(list)
        for v in D:groups[v&~m].append(v)
        for cell in groups.values():
            maxscore=None
            req=fixed&set(cell)
            adj={v:{v^(1<<d) for d in range(9) if m&(1<<d)}&set(cell) for v in cell}
            for pat in range(1<<len(cell)):
                T={v for j,v in enumerate(cell) if pat>>j&1}
                if not req<=T:continue
                z={v:sum(v^u for u in adj[v]&T) for v in T}
                if any(h not in valid[v,m] for v,h in z.items()):continue
                unseen=set(T);cycle=False
                while unseen:
                    a=[unseen.pop()]
                    for v in a:
                        nex=unseen&adj[v];unseen-=nex;a.extend(nex)
                    if sum(z[v].bit_count() for v in a)!=2*(len(a)-1):cycle=True;break
                if cycle:continue
                s=-sum(w.get((m,v,h),0) for v,h in z.items())
                maxscore=s if maxscore is None else max(s,maxscore)
            check(maxscore is not None,'no face option');total+=maxscore
    return total

def main():
    fixed={i:set(s) for i,s in map(json.loads,gzip.open('q9_high_port_290_survivor_facets.jsonl.gz','rt'))}
    lower=json.loads(open('q9_port_highdim_free_face.jsonl').readline())[-1]
    by_face=defaultdict(set);counts=Counter();controls=[];wins=[]
    for fn in ('q9_high_port_free_layer_trials.jsonl','q9_high_port_free_layer_narrow.jsonl','q9_high_port_free_layer_retry.jsonl'):
        for l in open(fn):
            r=json.loads(l);i=r['index']
            if i!='control' and r['status'] in ('DUAL','EXHAUSTED','EMPTY'):by_face[i].add((tuple(r['ports']),tuple(r['full'])))
    initial={i for i,S in fixed.items() if set(allowed(S))<=by_face[i]}
    goal_fits=lambda ep: (2,0) if ep==0 else (0,2)
    for fn in ('q9_high_port_free_whole.jsonl','q9_high_port_free_whole_runs.jsonl'):
        for l in open(fn):
            r=json.loads(l);i=r['index'];g=r['goal'];h=r['ep'];s=r['status']
            low=fixed[i] if i>=0 else {x for x in lower if x<256}
            pinned=low|set(([v for v in lower if v>=256][::3]) if i==-2 else [])
            D=low|{v+256 for v in range(256) if v not in low or len({v^(1<<d) for d in range(8)}&low)<=1}
            c=json.loads(Path(f'q9_high_port_free_whole_duals/r0_goal{g}_parent{i}_e{h}.json').read_text())
            check(c['parent']==sorted(low) and c['end_colour']==h and c['goal']==g,'bad input')
            v=value(c,pinned,D,g,h)
            check(v==r['integer_vertex_numerator']==c['upper'],'integer dual does not agree')
            if s=='DUAL_EXCLUSION':check(v<(g+1)*c['scale'],'bad exclusion')
            if s=='FOUND':
                path=r['witness'];ports={v for v in low if v+256 in path};full=tuple(sum(x.bit_count()%2==colour for x in (path[0],path[-1])) for colour in (0,1));check_path(path,low,ports,full,g)
            if i<0:
                controls.append([i,s,g]);continue
            counts[s]+=1
            if s=='FOUND':wins.append(i)
            if s in ('DUAL_EXCLUSION','EXHAUSTED'):
                by_face[i]|={b for b in allowed(low) if b[1]==goal_fits(h)}
    final={i for i,S in fixed.items() if set(allowed(S))<=by_face[i]}
    print(json.dumps(dict(case_status=counts,controls=controls,new_192_hits=wins,previous_fixed_port_exclusions=len(initial),extra_whole_face_exclusions=sorted(final-initial),verified_exclusions_among_290=sorted(final),remaining_among_290=290-len(final)),indent=2))
if __name__=='__main__':main()
