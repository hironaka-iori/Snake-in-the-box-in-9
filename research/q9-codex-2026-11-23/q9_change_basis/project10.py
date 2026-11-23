from pathlib import Path
from collections import Counter
from inputs import D,R
from check import audit
import random,sys,json,subprocess
def project_point(x,k,axis):
    if x&(1<<axis):x^=k
    return (x&((1<<axis)-1)) | ((x>>(axis+1))<<axis)
def run():
    n,step,ns,budget=map(int,sys.argv[1:]);rng=random.Random(16515+n)
    rows=[list(map(int,line.split()))[1:] for line in (R/'q9_three_seam_folds/q10_12.txt').read_text().splitlines()]
    windows=[(r,i) for r,p in enumerate(rows) for i in range(0,len(p)-n,step)]
    rng.shuffle(windows)
    for r,i in windows:
        original=rows[r][i:i+n+1];pairs=Counter(x^y for j,x in enumerate(original) for y in original[:j])
        span={0}
        for x in original:
            v=x^original[0]
            if v not in span:span |= {b^v for b in span}
        kernels=[k for k in range(1,1024) if pairs[k]<=2]
        inside=[k for k in kernels if k in span];reps=[k for k in kernels if k not in span]
        if reps:inside.append(rng.choice(reps))
        rng.shuffle(inside)
        for k in inside[:ns]:
            bit=k.bit_length()-1
            xs=sorted({project_point(x,k,bit) for x in original});holes=n+1-len(xs)
            assert holes==pairs[k]
            row='points '+' '.join(map(str,xs))+'\n'
            proc=subprocess.run([str(D/'augment'),str(n),str(budget),'0','grow'],input=row,text=True,check=True,capture_output=True)
            out=proc.stdout.splitlines();hit=next((v for v in out if v.startswith('FOUND')),None)
            un=[int(l.split()[2]) for l in out if l.startswith('FORM') and 'UNKNOWN' in l]
            p=None
            if hit:
                p,basis=audit(hit);inv=[0]
                for v in basis:inv += [z^v for z in inv]
                assert len(set(inv))==512 and set(xs)<={inv[z] for z in p} and len(p)>=n+1
            print(json.dumps(dict(source=r,offset=i,kernel=k,window_edges=n,holes=holes,unresolved=un,witness=p,found_line=hit)),flush=True)
            if p:return
if __name__=='__main__':run()
