from check import audit
from inputs import D,R,Random
import json,subprocess
rng=Random(44165)
def special():
    outcomes=[]
    for w in (R/'q9_gap_generations/prior191.words').read_text().split()[:10]:
        span={0};basis=[]
        while len(basis)<9:
            v=rng.randrange(1,512)
            if v in span or v.bit_count()<2:continue
            basis.append(v);span.update({x^v for x in span})
        p=[0]
        for a in w:p.append(p[-1]^basis[int(a)])
        rng.shuffle(p)
        row='points '+' '.join(map(str,p))+'\n'
        out=subprocess.run([str(D/'general'),'191','5000000','0'],input=row,text=True,capture_output=True,check=True).stdout
        hit=next((l for l in out.splitlines() if l.startswith('FOUND')),None)
        if hit:
            path,b=audit(hit);inv=[0]
            for a in b:inv+=[x^a for x in inv]
            assert {inv[z] for z in path}==set(p)
        outcomes.append(bool(hit))
    print(json.dumps(dict(gl9_scrambled_rows=outcomes)),flush=True)
if __name__=='__main__':special()
