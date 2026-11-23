from iso_solve import load
from sat import solve
import sys,json
def run(typ,kind,goal,start,limit,budget):
    ss,fs=load(typ)
    for j,(i,f) in enumerate(fs.items()):
        if j<start or j>=start+limit:continue
        p,ch=ss[i];S=set(p);U=S|set().union(*(a[2] for a in f));fixed=S-set().union(*(a[3] for a in f))
        if kind=='free':fixed=set()
        if kind=='open':
            for k in ch:fixed-=set(p[max(0,k-8):k+9])
        if kind=='phase':
            for k in ch:fixed-=set(p[max(0,k-5):k+6])
            # A real previously saved 191 sibling, when present, sets the model phase.
        if goal==191:colors=[None]
        else:colors=[0,1]
        for col in colors:
            r=solve(U,fixed,p,goal+1,budget,col);r.update(src=i,mode=kind,goal=goal,union=len(U),hard=len(fixed),majority=col)
            print(json.dumps(r,separators=(',',':')),flush=True)
            if goal==192 and r['path']:return
if __name__=='__main__':run(sys.argv[1],sys.argv[2],*map(int,sys.argv[3:]))
