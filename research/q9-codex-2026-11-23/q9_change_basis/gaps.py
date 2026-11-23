from inputs import D,R,Random,points
from check import audit
from subprocess import run,TimeoutExpired
import sys,json

def expand(index,goal,trials,seconds):
    rng=Random(517891+index);bank=(R/'q9_gap_generations/prior191.words').read_text().split()
    near=[w for w in (R/'q9_via_q10/monotone_near.words').read_text().split() if 192<=len(w)<=197]
    for t in range(trials):
        seed=rng.choice(bank if t%3==0 or goal<192 else near)
        p=points(seed);keep=set(p)
        k=rng.choice([4,5,6,7,8,9,10]) if goal>=192 else rng.choice([3,5,8,10])
        wanted=goal+1-k
        if wanted>len(keep) or wanted<1:continue
        defects=[(i,j) for i,a in enumerate(p) for j,b in enumerate(p[:max(0,i-1)]) if (a^b).bit_count()<2]
        indices=[i for pair in defects for i in pair]
        quantity=len(keep)-wanted
        if t%2 and indices:
            rng.shuffle(indices)
            for i in indices[:rng.randint(1,min(len(indices),max(1,quantity)))]: 
                if len(keep)>wanted:keep.discard(p[i])
        while len(keep)>wanted:
            if indices and rng.random()<0.7:z=p[max(0,min(len(p)-1,rng.choice(indices)+rng.randrange(-12,13)))]
            else:z=rng.choice(p)
            keep.discard(z)
        row='points '+' '.join(map(str,sorted(keep)))+'\n';pout=None;un=None;hit=None
        try:
            cp=run([str(D/'focus'),str(goal),'600000','0','grow'],input=row,text=True,capture_output=True,check=True,timeout=seconds)
            lines=cp.stdout.splitlines();un=[int(l.split()[2]) for l in lines if l.startswith('FORM') and 'UNKNOWN' in l]
            hit=next((l for l in lines if l.startswith('FOUND')),None)
            st='FOUND' if hit else ('UNKNOWN' if un else 'CLOSED')
            if hit:
                pout,b=audit(hit);inv=[0]
                for a in b:inv += [x^a for x in inv]
                assert keep<={inv[x] for x in pout} and len(pout)==goal+1
        except TimeoutExpired:st='TIME_LIMIT'
        print(json.dumps(dict(t=t,seed=seed,goal=goal,holes=k,removed=sorted(set(p)-keep),status=st,unresolved=un,path=pout,basis_record=hit)),flush=True)
        if pout and goal>=192:break
if __name__=='__main__':expand(*map(int,sys.argv[1:]))
