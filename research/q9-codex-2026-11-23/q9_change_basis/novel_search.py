from inputs import R,D,Random,points,norm
from check import audit,verify
from subprocess import run,TimeoutExpired
from pathlib import Path
import sys,json
def main(mode):
    bank=(R/'q9_gap_generations/prior191.words').read_text().split();seen={norm(w) for w in bank}
    for189=(R/'q9_gap_generations/prior189.words').read_text().split()
    for190=(R/'q9_gap_generations/prior190.words').read_text().split()
    near=[w for w in (R/'q9_via_q10/monotone_near.words').read_text().split() if len(w)>=192]
    rng=Random(113739)
    for case in range(10 if mode=='held' else 4200):
        w=rng.choice(bank if mode=='held' else [bank,for189,for190,near][case%4]);p=points(w);pts=set(p);ex=seen.copy()
        if mode=='held':
            ex.remove(norm(w));arcfile=D/'holdout.words';arcfile.write_text('\n'.join(sorted(ex))+'\n');k=case%3+1
        else:
            arcfile=R/'q9_gap_generations/prior191.words';k=rng.randint(3,10)
        while len(pts)>192-k:pts.remove(rng.choice(sorted(pts)))
        args=[str(D/'novel'),'191','500000','0','grow',str(arcfile)]
        hit=None;out=None;ex192=None
        try:
            r=run(args,input='points '+' '.join(map(str,sorted(pts)))+'\n',text=True,capture_output=True,check=True,timeout=8 if mode=='run' else 25)
            lines=r.stdout.splitlines();hit=next((s for s in lines if s.startswith('FOUND')),None)
            status='FOUND' if hit else ('UNKNOWN' if any('UNKNOWN' in s for s in lines) else 'CLOSED')
            if hit:
                out,b=audit(hit);inv=[0]
                for a in b:inv += [z^a for z in inv]
                assert pts<={inv[x] for x in out} and len(out)==192
                word=''.join(str((x^y).bit_length()-1) for x,y in zip(out,out[1:]));assert norm(word) not in ex
                for side in (out,out[::-1]):
                    for a in range(9):
                        cand=side+[side[-1]^(1<<a)]
                        if verify(cand):ex192=cand
        except TimeoutExpired:status='TIME_LIMIT'
        print(json.dumps(dict(row=case,source=w,holes=k,removed=sorted(set(p)-pts),status=status,path191=out,path192=ex192)),flush=True)
        if hit and mode=='run':break
if __name__=='__main__':main(sys.argv[1])
