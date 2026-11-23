"""Fix selected hybrid vertices on one side of a linear parity cut; allow any additional Q9 vertices."""
from pathlib import Path
import sys,json,random
from hashlib import sha256
D=Path(__file__).resolve().parent
sys.path.insert(0,str(D.parent))
from retry_q9_six_cube_cycle_cuts import search
from colors import violations
def main():
    kind,budget=sys.argv[1:];budget=int(budget);rng=random.Random(604151);processed=set();allQ=set(range(512))
    while True:
        if kind=='control':
            batch=[tuple(map(int,(D/'control.log').read_text().splitlines()[0].split()[9:]))]
        else:
            batch=[tuple(map(int,s.split()[2:])) for f in sorted(D.glob('common*.log')) for s in f.read_text().splitlines() if s.startswith('NEAR ')]
        queue=[p for p in batch if p not in processed]
        if not queue:break
        p=queue[0];processed.add(p);H=set(p);source=sha256(b''.join(v.to_bytes(2,'big') for v in p)).hexdigest()
        cuts=[(mask,side) for mask in range(1,512) for side in (0,1)]
        rng.shuffle(cuts)
        if kind=='control':cuts=cuts[:12]
        for mask,side in cuts:
            keep={v for v in H if ((v&mask).bit_count()&1)==side}
            status,q=search(keep,H,191 if kind=='control' else 192,budget,allowed=allQ)
            if q:assert len(q)>=192+(kind!='control') and not violations(q) and keep<=set(q)
            print(json.dumps(dict(mask=mask,side=side,source=source,fixed=len(keep),status=status,vertices=q),separators=(',',':')),flush=True)
            if q and kind!='control':return
if __name__=='__main__':main()
