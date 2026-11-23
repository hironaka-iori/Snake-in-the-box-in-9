from pathlib import Path
from random import Random
import argparse

def norm(w):
    labels={};return ''.join(str(labels.setdefault(c,len(labels))) for c in w)
def armlist(words):
    out=set()
    for w in words:
        for part in (w,w[::-1]):
            for pos in range(0,len(w)-95,6):
                out.add(norm(part[pos:pos+96]))
    return out
if __name__=='__main__':
    arg=argparse.ArgumentParser();arg.add_argument('old');arg.add_argument('out');arg.add_argument('seeds',nargs='+');param=arg.parse_args()
    old=armlist(''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:])) for l in Path(param.old).read_text().splitlines() if (p:=list(map(int,l.split()))))
    raw=set()
    for f in param.seeds:
        for line in Path(f).read_text().splitlines():
            a=line.split()
            if not a:continue
            if all(x in '012345678' for x in a[0]) and len(a[0])>=186:raw.add(a[0])
    arms=armlist(raw);rng=Random(74411)
    def emit(tag,arr):
        arr=sorted(arr);rng.shuffle(arr);Path(param.out+tag).write_text(''.join(w+'\n' for w in arr))
    emit('.new',arms-old);emit('.old',old);print(len(raw),len(arms),len(arms-old),len(old))
