from pathlib import Path
import sys,random,json
D=Path(__file__).resolve().parent;R=D.parent;sys.path.insert(0,str(R/'q9_change_basis'))
from inputs import points
def project(x,d):
    return (x&((1<<d)-1))|((x>>(d+1))<<d)
def main():
    near=(R/'q9_via_q10/monotone_near.words').read_text().split()
    known=(R/'q9_gap_generations/prior191.words').read_text().split()
    sets={}
    for w in known+near:
        pts=points(w)
        for d in range(9):
            s=tuple(sorted({project(x,d) for x in pts}))
            sets.setdefault(s,dict(word=w,sheet=d))
    rows=list(sets.items());random.Random(985111).shuffle(rows)
    with (D/'supports.txt').open('w') as f,(D/'sources.jsonl').open('w') as g:
        for s,ref in rows:
            print(*s,file=f);print(json.dumps(ref),file=g)
if __name__=='__main__':main()
