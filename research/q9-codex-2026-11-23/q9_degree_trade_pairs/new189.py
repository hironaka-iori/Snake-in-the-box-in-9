from pathlib import Path
from itertools import combinations
import subprocess,json,math
D=Path(__file__).resolve().parent
def valid(p):
    return len(set(p))==len(p) and all(((x^y).bit_count()==1)==(j+1==i) for i,x in enumerate(p) for j,y in enumerate(p[:i]))
def wordpath(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    assert valid(p)
    return p
def solve(dim,k,g,paths):
    inputtext="".join(" ".join(map(str,p))+"\n" for p in paths)
    out=subprocess.check_output([str(D/"gain"),str(dim),str(k),str(g)],text=True,input=inputtext)
    return [list(map(int,l.split())) for l in out.splitlines()]
def test():
    # A DFS on every ordered induced path starting at every Q3 vertex is a separate oracle.
    paths=[]
    def visit(p):
        paths.append(tuple(p))
        for d in range(3):
            v=p[-1]^1<<d
            if v not in p and all((v^x).bit_count()>1 for x in p[:-1]):visit(p+[v])
    for v in range(8):visit([v])
    seeds=[p for p in paths if 2<=len(p)<=4]
    total=positive=0
    for g in (1,2,3):
        for k in (0,1,2):
            bank=[p for p in seeds if len(p)>k]
            for p,(i,hit,n,_,__,*w) in zip(bank,solve(3,k,g,bank),strict=True):
                oracle=any(len(q)==len(p)+g and len(set(p)-set(q))==k for q in paths)
                assert bool(hit)==oracle
                if hit:assert valid(w) and len(w)==len(p)+g and len(set(p)-set(w))==k
                else:assert n==math.comb(len(p),k)
                total+=1;positive+=hit
    return total,positive
def main():
    words=(D.parent/"q9_uncovered_abab_20261121/outside_wordbanks189.words").read_text().split()
    bank=list(map(wordpath,words));assert len(bank)==16 and all(len(p)==190 for p in bank)
    print(json.dumps(dict(Q3_controls=test())),flush=True)
    for k in range(6):
        for gain in (3,2):
            for row,hit,n,viable,tested,*w in solve(9,k,gain,bank):
                if hit: assert len(w)==190+gain and valid(w) and len(set(bank[row])-set(w))==k
                else: assert n==math.comb(190,k)
                print(json.dumps(dict(row=row,deleted=k,gain=gain,deletion_sets=n,candidates=tested,found=hit,vertices=w)),flush=True)
                if hit and gain==3:return
if __name__=="__main__":main()
