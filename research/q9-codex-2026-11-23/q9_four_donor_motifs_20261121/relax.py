from pathlib import Path
import sys,time
root=Path(__file__).resolve().parent
sys.path.insert(0,str(root.parent/'q9_chord_remote_windows_20261121'))
from sat_replay import graph
if sys.argv[1]=='control':
    import subprocess
    p=[0]
    for x in (root.parent/'q9_three_axis_191.in').read_text().splitlines()[0]:p.append(p[-1]^(1<<int(x)))
    keep=set(p[:47])|set(p[50:95])|set(p[98:143])|set(p[146:])
    state,n,w=graph(keep,191,True);assert state=='FOUND'
    print(state,len(w)-1,*w);raise SystemExit
seen={};idx=0;stepping=sys.argv[1]=="stepping"
capmode=sys.argv[1]=='caps'
with (root/('caps.log' if capmode else 'wide.log')).open() as f:
    while True:
        l=f.readline()
        if not l:time.sleep(.25);continue
        if l.startswith('DONE') or l.startswith('FOUND'):break
        if not l.startswith('REPLAY' if capmode else 'FIELD'):continue
        idx+=1
        if stepping and idx%3!=1:continue
        labels,raw=l.split(' vertices');arcs=[];vs=list(map(int,raw.split()));start=0
        for field in labels.split()[2:]:
            donor,side,interval=field.split('/');a,b=map(int,interval.split('-'));ln=b-a+1
            arcs.append(vs[start:start+ln]);start+=ln
        assert len(arcs)==4 and len(vs)==start and len(set(vs))==len(vs)
        # Free both tips of every donor segment. All in-between vertices are unrestricted.
        fixed=frozenset(v for seg in arcs for v in (seg if capmode else seg[2:-2]))
        if fixed in seen:print('DUP',idx,seen[fixed],flush=True);continue
        seen[fixed]=idx
        state,n,w=graph(set(fixed),191 if stepping else 192,True)
        print(state,idx,len(fixed),n,*(w or []),flush=True)
        if w and len(w)>=193:break
print('DONE fields',idx,'unique',len(seen),flush=True)

