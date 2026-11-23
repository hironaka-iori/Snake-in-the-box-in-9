"""Search the GL orbit after a reversible, degree-two permutation of F2^9."""
from inputs import D,R,points,Random
from check import audit
from itertools import combinations
from subprocess import Popen,PIPE
import json,sys

def run():
    mode=sys.argv[1];rng=Random(417871)
    archive=(R/'q9_gap_generations/prior191.words').read_text().split()
    if mode=='near':
        raw=[w for w in (R/'q9_via_q10/monotone_near.words').read_text().split() if len(w)==192]
        seeds=[w for w in raw if sum((x^y).bit_count()<2 for j,x in enumerate(points(w)) for y in points(w)[:max(0,j-1)])==2]
    else:seeds=archive
    if mode=='control':seeds=archive[:12]
    todo=[(i,a,b,c) for i in range(len(seeds)) for a,b in combinations(range(9),2) for c in range(9) if c not in (a,b)]
    rng.shuffle(todo)
    if mode=='control':todo=todo[:12]
    for i,a,b,c in todo:
        vs=points(seeds[i]);tx=lambda v:v^((1<<c) if (v&(1<<a) and v&(1<<b)) else 0)
        changed=[tx(x) for x in vs];assert len(set(changed))==len(vs)
        n=192
        if mode=='control':
            # Obscure the input with this nonlinear map, test its specified inverse and hide all coordinates.
            obscured=[tx(x) for x in changed];span={0};ds=[]
            while len(ds)<9:
                z=rng.randrange(1,512)
                if z in span or z.bit_count()<2:continue
                ds.append(z);span.update({x^z for x in span})
            lut=[0]
            for d in ds:lut += [y^d for y in lut]
            changed=[lut[x] for x in obscured];n=191
        process=Popen([str(D/'augment'),str(n),'300000','0','grow'],stdin=PIPE,stdout=PIPE,text=True)
        log=process.communicate('points '+' '.join(map(str,changed))+'\n')[0];assert process.returncode==0
        lines=log.splitlines();found=next((l for l in lines if l.startswith('FOUND')),None)
        unresolved=[int(l.split()[2]) for l in lines if l.startswith('FORM') and 'UNKNOWN' in l]
        p=None
        if found:
            p,basis=audit(found);lut=[0]
            for g in basis:lut += [v^g for v in lut]
            assert len(p)>=n+1 and set(changed)<={lut[x] for x in p}
        print(json.dumps(dict(seed=i,controls=[a,b],flipped=c,unresolved=unresolved,path=p,found_line=found)),flush=True)
        if found and mode!='control':break
if __name__=='__main__':run()
