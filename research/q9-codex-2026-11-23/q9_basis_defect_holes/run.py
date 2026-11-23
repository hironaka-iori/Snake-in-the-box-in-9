from pathlib import Path
import sys,json,subprocess,time,random,collections
from prep import D,R,path
def validate(p,d=9):
    assert len(p)==len(set(p)) and all(0<=u<1<<d for u in p)
    for j,u in enumerate(p):
        for i in range(j):assert ((p[i]^u).bit_count()==1)==(i+1==j)
def verify(hit,core,goal):
    a,b=hit.split(' path ');basis=list(map(int,a.split(' basis ')[1].split()));assert len(basis)==9;p=list(map(int,b.split()));validate(p);assert len(p)==goal+1
    table=[0]
    for v in basis:table.extend([x^v for x in table])
    assert len(set(table))==512 and set(core)<={table[x] for x in p}
    return dict(basis=basis,path=p,new_input_points=sorted({table[x] for x in p}-set(core)))
def solve(row,cap,goal=192,mask=0):
    pts=row['points'];line='points '+' '.join(map(str,pts))+'\n';start=time.monotonic()
    res=subprocess.run([str(R/'q9_change_basis/augment'),str(goal),str(cap),str(mask),'augment'],input=line,text=True,capture_output=True,check=True)
    forms={};hit=None
    for s in res.stdout.splitlines():
        if s.startswith('FORM '):
            _,_,m,status,n,closed,rank=s.split();forms[int(m)]=(status,int(n),int(closed),int(rank))
        elif s.startswith('FOUND '):hit=verify(s,pts,goal)
    eligible={m for m in range(1,512) if (not mask or m==mask) and abs(sum(1-2*((x&m).bit_count()%2) for x in pts))<=goal+1-len(pts)+(goal+1)%2}
    if hit is None:assert set(forms)==eligible
    return dict(result='FOUND' if hit else 'UNKNOWN' if any(t[0]=='UNKNOWN' for t in forms.values()) else 'CLOSED',eligible=len(eligible),forms=len(forms),searched_nodes=sum(t[1] for t in forms.values()),basis_completions=sum(t[2] for t in forms.values()),unknown=[m for m,t in forms.items() if t[0]=='UNKNOWN'],seconds=round(time.monotonic()-start,3),**({'witness':hit} if hit else {}))
def main(mode,cap,mask=0):
    rows=[json.loads(l) for l in (D/(mode+'.jobs')).read_text().splitlines()]
    dest=D/(mode+'.results');goal=191 if mode=='controls' else 192
    with dest.open('w') as f:
        for i,row in enumerate(rows):
            result=solve(row,cap,goal,mask);print(json.dumps(dict(i=i,**result),separators=(',',':')),file=f,flush=True)
            if 'witness' in result and goal==192:print('FOUND192',mode,i,flush=True);break
if __name__=='__main__':main(sys.argv[1],int(sys.argv[2]),int(sys.argv[3]) if len(sys.argv)>3 else 0)
