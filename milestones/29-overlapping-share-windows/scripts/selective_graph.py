"""Diagnostic graph refinement using only a capped run of singleton count four.

Cycle means are checked exactly; this does not certify global minimum means,
the solver-derived share table, endpoint accounting, or a new snake bound.
"""
import hashlib,itertools,json,subprocess,sys,time
from fractions import Fraction
from pathlib import Path
from joint import HERE,ROOT,candidates,dkey
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from cache_obstruction import load_functions,induced,np
from packing import cache,key,canon
REF='8ad204ffa32bb3bb114891ab089a50b83d0fc10e'
def trailing(a):
    r=0
    for v in a[::-1]:
        if v!=4:break
        r+=1
    return r
def main():
    t=time.monotonic();lb,ex,_=cache();ub={}
    ex|={key(d,a) for d,a in json.loads((ROOT/'milestones/28-direct-share-certificates/data/exclusion-keys.json').read_text())}
    path='milestones/11-local-ceiling/s0_share_loop/share_oracle.jsonl'
    raw=subprocess.check_output(['git','-c','safe.directory=E:/Snake-in-a-box','show',f'{REF}:{path}'],cwd=ROOT)
    cachepath='milestones/10-window-aggregate/data/oracle_cache.jsonl'
    base_raw=subprocess.check_output(['git','-c','safe.directory=E:/Snake-in-a-box','show',f'{REF}:{cachepath}'],cwd=ROOT)
    known={}
    for line in base_raw.splitlines():
        if not line.strip():continue
        r=json.loads(line)
        if r['radius']==4:known[key(r['dirs'],r['alpha'])]=r['status']
    ex|={k for k,v in known.items() if v=='UNSAT'}
    for line in raw.splitlines():
        r=json.loads(line);k=key(r['dirs'],r['alpha'])
        if r['kind']=='plain' and r['result']=='UNSAT':ex.add(k)
        elif r['kind']=='thr' and r['result']=='UNSAT':lb[k]=max(lb.get(k,0),r['T'])
        if r['witness'] is not None:ub[k]=min(ub.get(k,10**6),r['witness'])
    shapes=[()]
    for length in range(7):
        shapes=[c+(d,) for c in shapes for d in range(min(max(c,default=-1)+2,9)) if induced(c+(d,))]
    states=[]
    for c in shapes:
        for a in itertools.product(range(1,7),repeat=4):
            for run in ([4,5,6] if a==(4,4,4,4) else [trailing(a)]):states.append((c,a,run))
    assert len(shapes)==34 and len(states)==44132
    sid={s:i for i,s in enumerate(states)};special={dkey(c['dirs']) for c in candidates()}
    direction_edges={c:[(c+(d,),canon(c[1:]+(d,))) for d in range(min(max(c)+2,9)) if induced(c+(d,))] for c in shapes}
    U=[];V=[];LO=[];HI=[];CUT=[];records=[]
    for u,(c,a,run) in enumerate(states):
        for ds,nc in direction_edges[c]:
            for s in range(1,7):
                al=a+(s,);keys=[key(ds[-k-1:],tuple((z,z) if z<6 else (6,21) for z in al[-k:])) for k in range(2,6)]
                if any(k in ex for k in keys):continue
                nr=min(6,run+1) if s==4 else 0;v=sid[(nc,al[1:],nr)]
                U.append(u);V.append(v);LO.append(120*s+lb.get(keys[-1],0));HI.append(120*s+ub.get(keys[-1],10**6))
                CUT.append(run==6 and s==4 and dkey(ds) in special)
                records.append((ds,s,keys[-1]))
    U=np.array(U);V=np.array(V);LO=np.array(LO);HI=np.array(HI);CUT=np.array(CUT)
    ns,algsha=load_functions();out=dict(scope='Exact recorded cycle means only; no global bound or minimum-mean certificate.',oracle_commit=REF,oracle_sha256=hashlib.sha256(raw).hexdigest(),base_oracle_sha256=hashlib.sha256(base_raw).hexdigest(),algorithm_sha256_lf=algsha,script_sha256_lf=hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest(),states=len(states),added_states=68,unpruned_edges=len(U),removed_edges=int(CUT.sum()),runs=[])
    print('built',len(states),'states;',len(U),'edges;',int(CUT.sum()),'new exclusions',flush=True)
    for label,mask in [('before',np.ones(len(U),dtype=bool)),('after',~CUT)]:
        pool=np.flatnonzero(mask);ids=pool[ns['prune'](len(states),U[pool],V[pool])]
        for mode,weights in [('lower',LO),('witness',HI)]:
            _,cyc=ns['howard'](len(states),U[ids],V[ids],weights[ids]);edges=[int(ids[e]) for e in cyc]
            assert all(V[e]==U[edges[(j+1)%len(edges)]] for j,e in enumerate(edges))
            assert all(not CUT[e] for e in edges) if label=='after' else True
            mean=Fraction(sum(int(weights[e]) for e in edges),120*len(edges))
            details=[dict(state=states[int(U[e])],next_state=states[int(V[e])],directions=records[e][0],alpha=records[e][1],five_window_key=records[e][2],weight=int(weights[e])) for e in edges]
            r=dict(stage=label,table=mode,pruned_edges=len(ids),period=len(edges),mean=str(mean),mean_decimal=float(mean),cycle=details)
            out['runs'].append(r);print(label,mode,str(mean),'period',len(edges),flush=True)
    out['seconds']=time.monotonic()-t
    (HERE/'data/selective-graph.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main()
