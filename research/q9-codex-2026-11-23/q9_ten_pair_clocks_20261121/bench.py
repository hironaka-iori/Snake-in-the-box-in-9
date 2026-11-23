from pathlib import Path
import sys,random,json
D=Path(__file__).resolve().parent;R=D.parent;sys.path.insert(0,str(R/'q9_pair_clocks'))
from search import lift
def solvefile(src,count,cap):
    rows=(D/(src+'.tsv')).read_text().splitlines();rng=random.Random(314682)
    count=min(count,len(rows));head=count//2
    ids=list(range(head))+rng.sample(range(head,len(rows)),count-head)
    for j in ids:
        row,start,ix,axes,cost,group,w=rows[j].split()
        s,p,c=lift(list(map(int,w)),((0,1),(2,3),(4,5),(6,7)),8,cap)
        print(json.dumps(dict(j=j,row=int(row),start=int(start),ix=int(ix),status=s,conflicts=c,path=p),separators=(',',':')),flush=True)
        if p and len(p)>=193:break
if __name__=='__main__':solvefile(sys.argv[1],int(sys.argv[2]),int(sys.argv[3]))
