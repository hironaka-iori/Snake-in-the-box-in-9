from control_common import *
from pathlib import Path
import subprocess

def damaged_end(p):
    for i in range(3,10):
        for a in range(9):
            for b in range(a):
                def image(x):
                    u=x^p[i]
                    return x^((1<<a)|(1<<b)) if ((u>>a)^(u>>b))&1 else x
                q=[image(v) for v in p[:i]]+p[i:]
                if len(defects(q) or [])==1:return q,i,a,b
    raise AssertionError
a,ia,xa,ya=damaged_end(p)
b,ib,xb,yb=damaged_end(p[::-1]);b.reverse()
data='\n'.join(' '.join(map(str,q)) for q in (a,b))+'\n'
r=subprocess.run(['/tmp/q9_binary_cross_20261121','100','53131','2'],input=data,capture_output=True,text=True,check=True).stdout
assert r.startswith('FOUND')
w=list(map(int,r.split('vertices')[1].split()))
assert len(w)==len(p) and defects(w)==[]
print('Damaged two different ends; first cut,axes',ia,xa,ya,'last cut,axes',ib,xb,yb,'chords',defects(a),defects(b),'verified',len(w)-1,'edges')
print(r.strip())
