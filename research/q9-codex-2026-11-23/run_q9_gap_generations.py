"""Iterate variable-length bridges, independently verifying new classes before reuse."""
import fcntl,json,subprocess
from pathlib import Path
from itertools import combinations
root=Path("q9_gap_generations");root.mkdir(exist_ok=True)
lock=(root/"run.lock").open("a");fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
def canon(word):
    def one(w):
        order={};return "".join(order.setdefault(c,str(len(order))) for c in w)
    return min(one(word),one(word[::-1]))
def load(p):return {canon(l) for l in Path(p).read_text().splitlines() if l}
def write(p,rows):p.write_text("".join(w+"\n" for w in sorted(rows)))
def vertices(w):
    p=[0]
    for c in w:
        assert c in "012345678"
        p.append(p[-1]^(1<<int(c)))
    return p
def check(p):
    assert len(p)==len(set(p)) and all(0<=v<512 for v in p)
    assert all(((p[i]^p[j]).bit_count()==1)==(j==i+1) for i,j in combinations(range(len(p)),2))
known={n:load("q9_gap_known%d.words"%n) for n in (189,190)}
known[191]=load("q9_reordered_segments_20261120/reference191.words")
wave=load("q9_gap_harvest_189.words");known[189]|=wave
for generation in range(1,9):
    seeds=root/f"round{generation}_inputs.words";write(seeds,wave)
    if not wave:break
    fresh=set()
    for target,trials in [(190,320000),(191,120000),(192,100000),(189,180000)]:
        stem=root/f"round{generation}_target{target}"
        out=stem.with_suffix(".words");log=stem.with_suffix(".log");checked=stem.with_suffix(".json")
        if not checked.exists():
            cmd=["/tmp/q9var-harvest-21",str(trials),str(target),str(80971+111*generation+target),str(3+generation%3),str(5+generation%4),"7500","2000"]
            if target!=192:
                previous=root/f"prior{target}.words";write(previous,known[target]);out.write_text("")
                cmd +=[str(previous),str(out)]
            with seeds.open() as inp,log.open("w") as dst:subprocess.run(cmd,stdin=inp,stdout=dst,check=True)
            lines=log.read_text().splitlines();found=[]
            for line in lines:
                if line.startswith(("FOUND ","EXTENDED ")):
                    t=line.split();p=list(map(int,t[3:] if t[0]=="FOUND" else t[1:]));check(p)
                    assert len(p)>=193;found=p;break
            if found:
                (root/"witness192.json").write_text(json.dumps(found));print("FOUND",flush=True);raise SystemExit
            end=lines[-1].split();assert end[:2]==["AT",str(trials)]
            candidates=load(out) if target!=192 else set()
            for w in candidates:
                assert w not in known[target] and len(w)==target;check(vertices(w))
            assert len(candidates)==int(end[4])
            checked.write_text(json.dumps(dict(generation=generation,target=target,trials=trials,new_classes=len(candidates),cutoffs=int(end[2]))))
        if target!=192:
            candidates=load(out)
            known[target]|=candidates;fresh|=candidates
        print(checked.read_text(),flush=True)
    wave=fresh
