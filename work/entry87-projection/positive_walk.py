"""Compare small complete substitution balls and literal positive repairs."""
from itertools import combinations,product
import json
from pathlib import Path
import subprocess
from solve import paths,defects


def replay(binary,path,k,lo=1,hi=192):
    p=subprocess.run([str(binary.resolve()),str(k),str(lo),str(hi)],input=" ".join(map(str,path)),
                     text=True,capture_output=True,check=True)
    return json.loads(p.stdout)


def check():
    binary=Path("transition-ball.exe")
    p,q=paths()
    assert len(q)==193
    # An implementation-independent radius-one enumeration reconstructs every
    # edited path, tests actual vertex identities and finds the first bad pair.
    def valid(path):
        occupied=set()
        for i,x in enumerate(path):
            if x in occupied: return False
            if any((x^(1<<b)) in occupied and (i==0 or path[i-1]!=(x^(1<<b))) for b in range(9)):
                return False
            occupied.add(x)
        return True
    valid_count=0
    for t in range(1,len(q)):
        d=q[t]^q[t-1]
        for b in range(9):
            if (1<<b)==d: continue
            candidate=q[:t]+[v^d^(1<<b) for v in q[t:]]
            valid_count+=valid(candidate)
    assert valid_count==0
    # Change one of the 191 transitions of the known valid source. At least
    # one repair exists in the resulting one-step ball (namely the source).
    assert replay(binary,p,0,1,len(p)-1)["status"]=="SAT"
    for t in (1,7,95,190):
        d=p[t]^p[t-1]
        b=next(1<<i for i in range(9) if (1<<i)!=d)
        altered=p[:t]+[v^d^b for v in p[t:]]
        repaired=replay(binary,altered,1,t,t)
        assert repaired["status"]=="SAT" and not defects(repaired["vertices"])
    return valid_count


if __name__=="__main__":
    print("Literal one-edit repairs:",check())
