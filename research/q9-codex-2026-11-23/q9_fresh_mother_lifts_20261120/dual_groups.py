"""Capture exact certificates for two free outer arms from the project's LP factorization."""
import argparse
import gzip
import itertools
import json
import random
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from search_q9_two_tip_lift import build

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument('words');parser.add_argument('output');parser.add_argument('--parts',type=int,default=8)
    parser.add_argument('--unresolved-log',help='Only produce records whose earlier LP needed branching')
    args=parser.parse_args()
    awaiting=None
    if args.unresolved_log:
        entries=[json.loads(line) for line in Path(args.unresolved_log).read_text().splitlines()]
        awaiting={(row,parity) for row,parity,_,state,_,_ in entries if state!='DUAL_EXCLUSION'}
    axes=list(itertools.combinations(range(8),3));random.Random(314).shuffle(axes)
    with gzip.open(args.output,'wt') as out:
        for row,w in enumerate(Path(args.words).read_text().split()):
            arm=[0]
            for c in w:arm.append(arm[-1]^(1<<int(c)))
            for parity in (0,1):
                if awaiting is not None and (row,parity) not in awaiting:continue
                result=build(arm,parity,192,axes[:args.parts])
                if result is None:raise ValueError("An empty factor requires separate verification")
                const,scale,factors,cert=result
                bound=const+sum(x[0][2] for _,x in factors)
                record=dict(word=w,outer_parity=parity,bound=bound,certificate=cert)
                out.write(json.dumps(record,separators=(',',':'))+'\n')
                out.flush()
                print(w,parity,bound,scale,193-len(arm),flush=True)
