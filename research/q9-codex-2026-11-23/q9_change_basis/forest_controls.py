from inputs import D,R,Random
from check import audit
import json,subprocess
rng=Random(8861)
def main():
    for i,w in enumerate((R/'q9_gap_generations/prior191.words').read_text().split()[:16]):
        span={0};basis=[]
        while len(basis)<9:
            v=rng.randrange(1,512)
            if v in span or v.bit_count()<2:continue
            basis.append(v);span.update({x^v for x in span})
        p=[0]
        for a in w:p.append(p[-1]^basis[int(a)])
        k=i%4+1;missing=rng.sample(range(1,len(p)-1),k);kept=[v for j,v in enumerate(p) if j not in missing]
        rng.shuffle(kept);row='points '+' '.join(map(str,kept))+'\n'
        out=subprocess.run([str(D/'augment'),'191','1500000','0','grow'],input=row,text=True,capture_output=True,check=True).stdout
        line=next((l for l in out.splitlines() if l.startswith('FOUND')),None)
        if line:
            found,b=audit(line);inv=[0]
            for a in b:inv += [x^a for x in inv]
            assert set(kept)<={inv[z] for z in found} and len(found)==192
        print(json.dumps(dict(case=i,holes=k,held_out=missing,found=bool(line))),flush=True)
if __name__=='__main__':main()
