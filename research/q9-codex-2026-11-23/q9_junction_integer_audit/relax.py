"""Re-optimize weakly anchored superset bounds, then minimize the required vertex set."""
from search import *
from verify_q9_high_port_whole import value
from itertools import combinations
import random

def assess(F,X,ep,count,tag,dest):
    P,A,why=simplify(F,X,192,ep)
    if why:return dict(index=tag,status='GEOMETRY',reason=why),None
    from search_q9_shell_dual import build
    os.environ['Q9_SHELL_PARTS']=str(count)
    r=build(sorted(F),0,ep,192,P,A)
    if r is None:return dict(index=tag,status='EMPTY'),None
    _,upper,_,_,c=r
    check=value(c,P,A,192,ep)
    assert upper==check
    c.update(index=tag,upper=upper,ep=ep,fixed=sorted(F),excluded=sorted(X))
    cpath=dest/f'{tag}.json';cpath.write_text(json.dumps(c,separators=(',',':'))+'\n')
    return dict(index=tag,status='DUAL_EXCLUSION' if upper<193*c['scale'] else 'OPEN',fixed=sorted(F),excluded=sorted(X),ep=ep,upper=upper,faces=count),c

def main():
    dest=Path(__file__).parent/'relaxed_duals';dest.mkdir(exist_ok=True)
    raw=set(load('q9_junction_first_omission.jsonl')[0]['fixed'])
    best={}
    for ep in (0,1):
        for n in (16,28):
            r,c=assess(raw,set(),ep,n,f'full75_e{ep}_n{n}',dest);print(json.dumps(r,separators=(',',':')),flush=True)
            if r['status']=='DUAL_EXCLUSION':best[ep]=(raw,set(),c);break
    if 0 not in best:
        for X in ({26},{508},{26,508}):
            r,c=assess(raw,X,0,18,'full75_x'+'_'.join(map(str,sorted(X))),dest);print(json.dumps(r,separators=(',',':')),flush=True)
            if r['status']=='DUAL_EXCLUSION':best[0]=(raw,X,c);break
    for ep,(F,X,c) in best.items():
        F=set(F);rng=random.Random(29834)
        for iteration in range(6):
            # Favor removals which geometrically increase the allowed domain least.
            options=[]
            for v in F:
                req,domain,reason=simplify(F-{v},X,192,ep)
                options.append((len(domain),-len(req),rng.random(),v,req,domain))
            choices=[]
            for _,_,_,v,P,A in sorted(options)[:12]:
                n=value(c,P,A,192,ep);choices.append((n,v))
            n,v=min(choices)
            if n>=193*c['scale']:
                r,new=assess(F-{v},X,ep,22,f'refit{len(F)-1}_e{ep}',dest);print(json.dumps(r,separators=(',',':')),flush=True)
                if r['status']!='DUAL_EXCLUSION':break
                c=new
            else:
                P,A,why=simplify(F-{v},X,192,ep)
                c={**c,'fixed':sorted(F-{v}),'upper':n,'index':f'rem{len(F)-1}_e{ep}'}
                (dest/(c['index']+'.json')).write_text(json.dumps(c,separators=(',',':'))+'\n')
                print(json.dumps(dict(index=c['index'],status='DUAL_EXCLUSION',fixed=c['fixed'],excluded=c['excluded'],ep=ep,upper=n,faces=len(c['axes'])),separators=(',',':')),flush=True)
            F.remove(v)

if __name__=='__main__':main()
