from collections import Counter
from pathlib import Path
import json
D=Path(__file__).resolve().parent;bank=D.parent/'q9_three_seam_folds/q10_12.txt'
def section(p,m,b):
    pivot=(m&-m).bit_length()-1
    return sorted((x&((1<<pivot)-1))|((x>>(pivot+1))<<pivot) for x in p if (x&m).bit_count()%2==b)
def main():
    data=[list(map(int,l.split()))[1:] for l in bank.read_text().splitlines()];counts=Counter()
    with (D/'sections.pts').open('w') as f:
        for i,p in enumerate(data):
            assert len(p)==len(set(p))==380 and all(0<=v<1024 for v in p)
            assert all(((x^y).bit_count()==1)==(j==k+1) for j,y in enumerate(p) for k,x in enumerate(p[:j]))
            for m in range(1,1024):
                for b in (0,1):
                    values=section(p,m,b);counts[len(values)]+=1;print(i,m,b,len(values),*values,file=f)
    print(json.dumps(dict(total=sum(counts.values()),minimum=min(counts),maximum=max(counts),counts=dict(sorted(counts.items()))),indent=2))
if __name__=='__main__':main()
