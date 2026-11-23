from pathlib import Path
import subprocess
p=list(map(int,open('q9_four_piece_191_seeds.txt').readline().split()))
def defects(q):
    assert all(0<=v<512 for v in q)
    if len(set(q))!=len(q) or any((a^b).bit_count()!=1 for a,b in zip(q,q[1:])):
        return None
    return [(j,i) for i,a in enumerate(q) for j,b in enumerate(q[:max(0,i-1)]) if (a^b).bit_count()==1]
assert len(p)==192 and defects(p)==[]
