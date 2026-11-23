"""Plant a fresh outside arc, release nearby old vertices and solve for the remaining vertices and the basis."""
from inputs import R,D,Random,points
from check import audit,verify
from subprocess import run,TimeoutExpired
import json,sys
def main(goal,trials,seed):
    rng=Random(seed);known=(R/'q9_gap_generations/prior191.words').read_text().split()
    near=[w for w in (R/'q9_via_q10/monotone_near.words').read_text().split() if 192<=len(w)<=196]
    num=0
    for trial in range(trials*300):
        w=rng.choice(known if trial%2==0 else near)
        p=points(w);old=set(p);ix={x:i for i,x in enumerate(p)}
        anchor=rng.choice(p);arc=[anchor];desired=rng.randint(2,7)
        for _ in range(desired):
            ds=list(range(9));rng.shuffle(ds);options=[]
            for d in ds:
                y=arc[-1]^(1<<d)
                if y in old or any((y^z).bit_count()<2 for z in arc[:-1]):continue
                touch=[y^(1<<a) for a in range(9) if y^(1<<a) in old and y^(1<<a)!=anchor]
                options.append((len(touch)+rng.random()*3,y))
            if not options:break
            arc.append(min(options)[1])
        if len(arc)<3:continue
        # Release original vertices that would conflict with an internal vertex of the new arc.
        release={y^(1<<a) for y in arc[1:] for a in range(9) if y^(1<<a) in old}
        release.discard(anchor)
        k=goal+1-(len(old)-len(release)+len(arc)-1)
        if k<1 or k>11:continue
        if len([v for v in release if abs(ix[v]-ix[anchor])<12])>len(release)-1:continue
        retained=(old-release)|set(arc);assert len(retained)==goal+1-k
        line='points '+' '.join(map(str,sorted(retained)))+'\n';hit=None;pout=None
        try:
            cp=run([str(D/'focus'),str(goal),'420000','0','grow'],input=line,text=True,capture_output=True,timeout=6,check=True)
            lines=cp.stdout.splitlines();hit=next((x for x in lines if x.startswith('FOUND')),None)
            st='FOUND' if hit else 'UNKNOWN' if any('UNKNOWN' in x for x in lines) else 'CLOSED'
            if hit:
                pout,b=audit(hit);inv=[0]
                for d in b:inv+=[x^d for x in inv]
                assert retained<={inv[x] for x in pout} and len(pout)==goal+1
        except TimeoutExpired:st='TIME_LIMIT'
        print(json.dumps(dict(row=num,trial=trial,seed=w,arc=arc,released=sorted(release),target=goal,holes=k,status=st,path=pout,record=hit)),flush=True)
        num+=1
        if hit or num==trials:break
if __name__=='__main__':main(*map(int,sys.argv[1:]))
