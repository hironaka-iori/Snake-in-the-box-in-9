"""Locate the full-cube forbidden middles in every archived 190- and 191-edge path."""
from collections import Counter
from pathlib import Path
import sys
from middles import BASE,HERE,read,save,shape
sys.path.insert(0,str(BASE))
from archive import input_paths
from overlap import transitions,normal,literal_isometry


def main():
    results=read(HERE/'coverage.json')['rows']
    geometry=read(HERE/'geometry.json')
    before=read(next(HERE.parent.glob('281-*'))/'coverage.json')['paths']
    old=read(BASE/'consecutive-overlap.json')['paths']
    known={}
    for k,r in results.items():
        if r['upper'] is not None and r['upper']<192:
            p=geometry[k]['middle']
            known.setdefault(len(p)-1,{})[shape(p)]=(k,p)
    rows={}
    counts={190:Counter(),191:Counter()}
    for tag,path in input_paths():
        w=transitions(path)
        n=len(w)
        hits=[]
        for length,bucket in known.items():
            for offset in range(n-length+1):
                word=w[offset:offset+length]
                found=bucket.get(min(normal(word),normal(word[::-1])))
                if found:
                    key,m=found
                    assert literal_isometry(m,path[offset:offset+length+1])
                    hits.append([offset,offset+length,key])
        family=old[tag]['cover']+before[tag]['matches']+hits
        bound=max(min((hi-1 for lo,hi,*_ in family if lo>=i),default=n)-i for i in range(n+1))
        assert bound<=before[tag]['upper']
        if hits:
            counts[n]['paths_containing_a_middle']+=1
            counts[n]['occurrences']+=len(hits)
        counts[n]['improved_over_281']+=int(bound<before[tag]['upper'])
        counts[n]['largest_bound']=max(counts[n]['largest_bound'],bound)
        rows[tag]=dict(bound=bound,new_matches=hits)
    save(HERE/'archive-transfer.json',dict(summary=counts,paths=rows))
    print('Full-cube exclusions applied to both archives',counts)


if __name__=='__main__':
    main()
