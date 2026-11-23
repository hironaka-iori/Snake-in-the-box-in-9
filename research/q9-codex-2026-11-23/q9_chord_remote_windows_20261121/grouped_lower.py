from sat_replay import graph,keep
from pathlib import Path
from collections import Counter
import sys,subprocess
D=Path(__file__).resolve().parent
if len(sys.argv)>1:
    p=list(map(int,subprocess.check_output(['python3',str(D/'control_input.py')]).split()))
    st,n,w=graph(keep(p,13,17,2,6),190,True);assert st=='FOUND' and len(w)>=191
    print(st,len(w)-1,*w);raise SystemExit
bank=[list(map(int,s.split())) for s in Path('q9_all_newsingle_hinge.vertices').read_text().splitlines()]
for row,p in enumerate(bank):
    (x,y),=[(i,j) for i,a in enumerate(p) for j in range(i+2,len(p)) if (a^p[j]).bit_count()==1]
    for tip in [x,y]:
        a=max(0,tip-13);b=min(len(p)-1,tip+13)
        for start in range(0,len(p)-23+1,12):
            last=min(len(p)-23,start+11);c=start;e=last+22
            # Every nominal 23-window with start in [start,last] is contained in this released union.
            st,n,w=graph(keep(p,a,b,c,e),192,True)
            print(st,row,a,b,c,e,n,*(w or []),flush=True)
            if w:raise SystemExit
print('DONE',flush=True)

