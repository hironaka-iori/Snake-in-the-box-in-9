"""Regenerate the finite factor models and replay terminal EXHAUSTED rows with a fresh C++ binary."""
import argparse
import json
import os
from pathlib import Path

from search_q9_donor_port_branches import branch
from verify_q9_96_donor_coverage import snapshot, key, check

def main():
    p=argparse.ArgumentParser();p.add_argument('binary',type=Path);a=p.parse_args()
    os.environ.update(Q9_SHELL_SOLVER=str(a.binary.resolve()),Q9_PATH_MINIMUM='1')
    os.environ.pop('Q9_AVOID_SHAPES',None)
    tasks=[]
    for kind in ('hard96','last96'):
        prefix='q9_'+kind
        rows,complete=snapshot(prefix+'_port_duals.jsonl.gz')
        check(complete,'unfinished certificate file')
        states,_=snapshot(prefix+'_port_search.jsonl')
        table={i:(rows[i],s,n) for i,s,n,w in states}
        sources=[(prefix+'_retry.jsonl',prefix+'_retry_duals.jsonl.gz')]
        if kind=='last96':sources.insert(0,(prefix+'_early4_retry.jsonl',prefix+'_early4_d.jsonl.gz'))
        for fn,certfile in sources:
            certs=dict(snapshot(certfile)[0])
            for i,s,n,w,u in snapshot(fn)[0]:
                if s=='UNKNOWN':continue
                cert=certs[i]
                check(cert['word']==rows[i]['word'] and key(cert)==key(rows[i]),'mismatched retry')
                table[i]=cert,s,n
        for i,(r,status,n) in table.items():
            check(status in {'DUAL','EXHAUSTED'},'unresolved case')
            if status=='EXHAUSTED': tasks.append((n,kind,i,r))
    for n,kind,i,r in sorted(tasks,key=lambda t:t[:3]):
        status,visits,w=branch(r,192,n+1)
        check(status=='EXHAUSTED' and visits==n and w is None,'replayed search disagrees')
        print(json.dumps(dict(family=kind,index=i,nodes=visits,status=status)),flush=True)

if __name__=='__main__':main()
