from geom import *
from collections import Counter
import itertools
def main():
    summary={};best=None
    rows=list(map(json.loads,(R/'q9_lower_island_edge_20261121/cases.jsonl').read_text().splitlines()))
    for nm in ('mixed','deep','regrow'):
        paths=[]
        for line in (D/(nm+'.paths')).read_text().splitlines():
            i,n,*p=map(int,line.split());c=rows[i]
            assert 0<=min(p) and max(p)<512 and len(p)==len(set(p))==n+1 and len(c['w'])==93 and i not in range(1249,1253)
            for j,v in enumerate(p):
                for t in range(j):
                    assert ((v^p[t]).bit_count()==1)==(t==j-1)
            L=set(c['lo']+c['edge']);assert {v for v in p if v<256}==L
            port={min(v,w) for v,w in zip(p,p[1:]) if v^w==256};assert len(port)==3 and len(port&set(c['edge']))==1
            paths.append((n,i,p))
            if best is None or n>best['edges']:best=dict(edges=n,case=i,file=nm+'.paths',vertices=p,lower_word=c['w'],isolated_edge=c['edge'])
        if paths:
            n,i,p=max(paths);summary[nm]=dict(witnesses=len(paths),max_edges=n,case=i,segments=[(lo,len(list(xs))) for lo,xs in itertools.groupby(p,key=lambda v:v>>8)])
    (D/'best182.json').write_text(json.dumps(best,separators=(',',':'))+'\n')
    logs=(D/'mixed.log').read_text().splitlines();metrics=Counter()
    for ln in logs:
        t=ln.split()
        for i in range(1,len(t),2):metrics[t[i]]+=int(t[i+1])
    summary['mixed_operations']=metrics
    (D/'construction_summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary)
if __name__=='__main__':main()
