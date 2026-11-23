"""Independent parity-colour SAT formulation and all-pair validation."""
from pathlib import Path
import sys,json
from collections import Counter
import itertools
here=Path(__file__).resolve().parent
sys.path.insert(0,str(here.parent))
from repair_q9_time_projection import repair
from search import vertices,norm,old_keys
def check(p):
    assert all(0<=v<512 for v in p) and len(set(p))==len(p)
    adj=sum((a^b).bit_count()==1 for a,b in itertools.combinations(p,2))
    assert all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
    return adj-(len(p)-1)
def main():
    d=int(sys.argv[1]);budget=int(sys.argv[2])
    bank=(here.parent/'q9_three_axis.in').read_text().splitlines()
    control=json.loads((here/f'control{d}.json').read_text());seed=vertices(control[2]);axes=control[3];w=control[-1]
    mask=sum(1<<a for a in axes)
    assert len(seed)==len(w)==192 and check(seed)>0 and check(w)==0 and all((a&~mask)==(b&~mask) for a,b in zip(seed,w))
    # Check pairwise true path directly, then independently solve the same damaged instance.
    status,model=repair(seed,axes,180000)
    if model:assert len(model)==192 and check(model)==0
    print(json.dumps(['control',d,status,model]),flush=True)
    seen=old_keys(d)
    for f in sorted(here.glob(f'd{d}_*.jsonl')):
        for line in f.read_text().splitlines():
            trial,row,axes,H,constraints,old,_,w=json.loads(line)
            word=bank[row];sig=norm(word,axes)
            if sig in seen:continue
            seen.add(sig);seed=vertices(word)
            if w:assert check(w)==0 and len(w)==193
            status,model=repair(seed,axes,budget)
            if model:assert len(model)==193 and check(model)==0
            assert not (old=='UNSAT' and status=='FOUND')
            print(json.dumps([f.name,trial,row,axes,old,status,model],separators=(',',':')),flush=True)
            if model:return
if __name__=='__main__':main()
