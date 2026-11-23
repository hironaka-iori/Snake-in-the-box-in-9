"""Validate all logged snakes without relying on annealer metadata."""
from pathlib import Path
from collections import Counter
import json, hashlib

def signature(path):
    steps=[a^b for a,b in zip(path,path[1:])]
    def normalize(s):
        d={};return ''.join(str(d.setdefault(x,len(d))) for x in s)
    return min(normalize(steps),normalize(steps[::-1]))

def inspect(path,bank):
    assert len(path)==len(set(path)) and all(0<=x<512 for x in path)
    assert all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(path) for j,y in enumerate(path) if j>i)
    counts=sorted(Counter(a^b for a,b in zip(path,path[1:])).values(),reverse=True)
    counts+= [0]*(9-len(counts))
    return len(path)-1,counts,signature(path) in bank

def main():
    root=Path(__file__).resolve().parent
    bank=set((root/'known191.txt').read_text().split());assert len(bank)==131
    specs=json.loads((root/'manifest.json').read_text());out=[]
    for spec in specs:
        log=root/(spec['name']+'.log')
        rows=[line.split() for line in log.read_text().splitlines()]
        start=0 if spec['seed_file']=='-' else len((root/spec['seed_file']).read_text().split())
        assert int(rows[0][1])==start
        reports=[];targets=[];rejected=[];end={}
        for f in rows[1:]:
            if f[0]=='END':
                end={f[k]:int(f[k+1]) for k in range(1,len(f),2)};continue
            if f[0]=='SNAKE':
                p=list(map(int,f[5:]));length,vec,known=inspect(p,bank)
                assert length==int(f[2]) and max(vec,default=0)==int(f[3]) and known==bool(int(f[4]))
                reports.append((int(f[1]),length,vec,known))
            elif f[0] in ('TARGET','KNOWN_CANDIDATE'):
                p=list(map(int,f[3:]));length,vec,known=inspect(p,bank)
                assert length==int(f[2])
                if f[0]=='KNOWN_CANDIDATE':
                    assert known and length==191
                    rejected.append(dict(step=int(f[1]),edges=length,dcv=vec))
                else:
                    assert length>=192 or length==191 and not known
                    targets.append(dict(step=int(f[1]),edges=length,dcv=vec))
            else:raise ValueError(f[0])
        assert end or targets
        if end:
            assert end['proposals']==spec['proposals']
            assert end['best']==max([z[1] for z in reports],default=-1)
            assert end['gap_best']==max([z[1] for z in reports if 45<=z[2][0]<=51],default=-1)
        best=max(reports,key=lambda z:z[1]) if reports else None
        growth=[z for z in reports if z[0]>0]
        out.append(dict(**spec,actual_start_edges=start-1 if start else None,verified_reports=len(reports),best_accepted=best,best_accepted_update=max(growth,key=lambda z:z[1]) if growth else None,first_rejected_known=rejected,target=targets,end=end,sha256_log=hashlib.sha256(log.read_bytes()).hexdigest()))
    (root/'results.json').write_text(json.dumps(out,indent=1)+'\n')
    for d in out:print(d['name'],d['end'].get('best'),d['end'].get('gap_best'),d['end'].get('rejected_known'),len(d['target']))
if __name__=='__main__':main()
