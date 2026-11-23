from geom import *
import random,sys
sys.path.insert(0,str(R))
from verify_q9_intact98_all_crossings import integer_bound
def main():
    selected,_=regs();rng=random.Random(71053);by=defaultdict(list)
    for r in selected.values():by[r['file'].split('/')[0]].append(r)
    picked=[]
    for vals in by.values():
        vals=sorted(vals,key=lambda r:(r['i'],r['c']))
        picked.extend(rng.sample(vals,min(12,len(vals))))
        picked.extend([min(vals,key=lambda x:x['score']),max(vals,key=lambda x:x['score'])])
    picked={r['file']:r for r in picked}
    for r in picked.values():
        mask,h,*z=gzip.decompress((D/r['file']).read_bytes()).splitlines()
        ax=[[k for k in range(8) if m>>k&1] for m in map(int,mask.split())]
        i,c,score,scale,bal,x,y,_=map(int,h.split()[1:])
        L,P,m,eps,delta=geometry(i,c)
        cert=dict(axes=ax,scale=scale,end_weights=[x,y],balance_weight=bal,weights=[list(map(int,s.split())) for s in z])
        ans=len(L)*scale+integer_bound(cert,L,P,eps,delta)
        assert ans==score==r['score'] and score<193*scale
    (D/'python_replay.json').write_text(json.dumps(dict(samples=len(picked),files=sorted(picked)),indent=2)+'\n');print(len(picked))
if __name__=='__main__':main()
