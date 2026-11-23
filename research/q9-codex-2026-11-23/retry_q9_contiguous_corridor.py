"""Refine previously undecided corridor domains, retaining reconstruction details."""
import argparse,json,random
from pathlib import Path
from repair_q9_contiguous_corridor import search
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('bank',type=Path);p.add_argument('budget',type=int);p.add_argument('model',type=int)
    p.add_argument('logs',nargs='+',type=Path);p.add_argument('--reverse',action='store_true');p.add_argument('--limit',type=int)
    args=p.parse_args();bank=[list(map(int,l.split())) for l in args.bank.read_text().splitlines()]
    records={}
    for log in args.logs:
        for line in log.read_text().splitlines():
            d=json.loads(line);key=(d['row'],d['start'],d['k'])
            if key not in records or d['status']!='UNKNOWN':records[key]=d
    todo=[d for d in records.values() if d['status']=='UNKNOWN']
    if args.reverse:todo.reverse()
    if args.limit:todo=todo[:args.limit]
    for d in todo:
        d['status'],d['witness']=search(bank[d['row']],d['start'],d['k'],args.budget,args.model)
        print(json.dumps(d,separators=(',',':')),flush=True)
        if d['witness']:break
