from pathlib import Path
import sys,os,json
D=Path(__file__).resolve().parent;sys.path.insert(0,str(D.parent));import sat
sat.D=D;sat.W=(D/'donors.words').read_text().split();from banks import path
os.environ['Q9_NO_PINS']='1';os.environ['Q9_EXPORT_PROOF']='1'
for line in (D/'survey.seeds').read_text().splitlines():
    i,n,na,*z=map(int,line.split());a=z[:na];nb=z[na];b=z[na+1:];assert len(b)==nb
    ch=path(sat.W[i])[-1];dirs=[d for v in (1,0) for d in range(8) if (ch>>d)&1==v];un=lambda x:sum((x>>k&1)<<d for k,d in enumerate(dirs));arms=list(map(un,a)),list(map(un,b))
    for c in (0,1):sat.search(i,c,192,500000,arms)
