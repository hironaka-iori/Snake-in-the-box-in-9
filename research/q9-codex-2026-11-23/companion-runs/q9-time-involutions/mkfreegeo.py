from pathlib import Path
r=Path(__file__).resolve().parent;s=(r/'geo.py').read_text()
s=s.replace('D=dom(p,win,active);n=len(p);idx=', '''D=dom(p,win,active);n=len(p)
 # Release both ends and choose one further vertex at each tip. In this model
 # they are free subject only to the exact global induced-path constraints.
 for j in (0,n-1):
  step=1 if j==0 else -1
  i=j+step
  D[i]|={x^(1<<d) for x in D[j+2*step] for d in range(9)}
  D[j]|={x^(1<<d) for x in D[i] for d in range(9)}
 idx=''')
(r/'freegeo.py').write_text(s)

