"""Fix independently enumerated snakes and check exact share caps on both sides."""
import json,random,time
from pathlib import Path
from direct import ROOT,HERE,census,solve

def dirs(path):return [(a^b).bit_length()-1 for a,b in zip(path,path[1:])]
def samples(n):
    rng=random.Random(196+n);out=[]
    for _ in range(12):
        p=[0]
        for j in range(rng.randrange(3,10)):
            choices=[p[-1]^(1<<a) for a in range(n)]
            rng.shuffle(choices)
            valid=[q for q in choices if q not in p and all((q^v).bit_count()!=1 for v in p[:-1])]
            if not valid:break
            p.append(valid[0])
        out.append(p)
    return out

def main():
    rows=[]
    for n in (3,4):
        for index,p in enumerate(samples(n)):
            c=census(set(p),n,p[1:-1])
            base=dict(name=f'q{n}_{index}',dimension=n,dirs=dirs(p),alpha=[[a,a] for a in c['alpha']])
            for offset,expected in [(0,'FEASIBLE'),(-1,'INFEASIBLE')]:
                r=solve(dict(base,cap=c['total_share']+offset),4,fixed=set(p))
                assert r['status']==expected,(base,r)
                rows.append(dict(name=base['name'],path=p,cap=c['total_share']+offset,status=r['status']))
    bank=json.loads((ROOT/'work/bank9.json').read_text())
    for bi,start in [(0,10),(0,80),(45,174),(130,30)]:
        p=bank[bi]['vertex_sequence'];z=p[start];S={v^z for v in p};win=[v^z for v in p[start:start+7]]
        c=census(S,9,win[1:-1]);base=dict(name=f'bank{bi}_{start}',dirs=dirs(win),alpha=[[a,a] for a in c['alpha']])
        for offset,expected in [(0,'FEASIBLE'),(-1,'INFEASIBLE')]:
            r=solve(dict(base,cap=c['total_share']+offset),8,fixed=S)
            assert r['status']==expected,(base,r)
            rows.append(dict(name=base['name'],bank_index=bi,start=start,cap=c['total_share']+offset,status=r['status']))
    out=dict(status='PASSED',cases=rows,count=len(rows))
    (HERE/'data/controls.json').write_text(json.dumps(out,indent=2)+'\n')
    print(out['status'],out['count'],flush=True)
if __name__=='__main__':main()
