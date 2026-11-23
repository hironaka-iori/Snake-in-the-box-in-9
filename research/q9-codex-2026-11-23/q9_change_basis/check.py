from inputs import D,R,points
from subprocess import run
from collections import Counter
import json

def verify(p):
    return all(0<=x<512 for x in p) and len(set(p))==len(p) and all(((x^y).bit_count()==1)==(i+1==j) for j,y in enumerate(p) for i,x in enumerate(p[:j]))
def audit(found):
    lhs,rhs=found.split(' path ');basis=list(map(int,lhs.split(' basis ')[1].split()))
    p=list(map(int,rhs.split()));assert verify(p) and len(basis)==9
    return p,basis
def main():
    stats=Counter()
    for k in [4,5,6,7]:
        for row in (D/f'control{k}.txt').read_text().splitlines():
            result=run([str(D/'find'),'191',str(k),str(k)],input=row+'\n',text=True,check=True,capture_output=True).stdout
            p,basis=audit(next(l for l in result.splitlines() if l.startswith('FOUND')))
            assert len(p)==192
            inv=[0]
            for a in basis:inv+= [x^a for x in inv]
            assert len(set(inv))==512 and {inv[z] for z in p}==set(map(int,row.split()[1:]))
            stats[k]+=1
    print(json.dumps(dict(controls=stats)))
if __name__=='__main__':main()
