"""Compare the compiled splice enumeration with an independent small-cube recursion."""
import argparse
import json
from pathlib import Path
import random
from solve import BANK,defects
from translated_splice import search


def literal(path,k):
    for i in range(len(path)-k-1):
        j=i+k+1
        for b in range(9):
            left=path[:i+1];right=[v^(1<<b) for v in path[j:]]
            if any((u^v).bit_count()<2 for u in left for v in right):continue
            def visit(q,steps):
                if not steps:return not defects(q+right)
                for t in range(9):
                    v=q[-1]^(1<<t)
                    if any((v^w).bit_count()<=1 for w in q[:-1]):continue
                    if v in right or any((v^w).bit_count()<=1 for w in right[1:]):continue
                    if (v^right[0]).bit_count()>steps:continue
                    if visit(q+[v],steps-1):return True
                return False
            if visit(left,k+1):return True
    return False


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--exe",type=Path,default=Path("translated-splice.exe"))
    exe=parser.parse_args().exe.resolve()
    rng=random.Random(6209);amount=0;positive=0
    for trial in range(60):
        q=[rng.randrange(512)];limit=rng.randint(4,22)
        for t in range(limit):
            options=[q[-1]^(1<<b) for b in range(6)]
            options=[v for v in options if all((v^w).bit_count()>=2 for w in q[:-1])]
            if not options:break
            q.append(rng.choice(options))
        for k in range(min(4,len(q)-1)):
            expected=literal(q,k)
            computed=search(q,k,k,1,exe)
            assert expected==("witness" in computed)
            amount+=1;positive+=expected
    for rec in json.loads(BANK.read_bytes())[:4]:
        for k in range(4):
            q=rec["vertex_sequence"]
            expected=literal(q,k)
            assert not expected and "witness" not in search(q,k,k,1,exe)
            amount+=1
    print(amount,positive,amount-positive,flush=True)
