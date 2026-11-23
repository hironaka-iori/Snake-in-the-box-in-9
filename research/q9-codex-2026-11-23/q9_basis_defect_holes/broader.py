from prep import *
import itertools,subprocess
raw=[json.loads(l) for l in (D/'minimal.jobs').read_text().splitlines()]
seedrows={}
for r in raw:seedrows.setdefault(r['seed'],[]).append(r)
def stream():
 for seed,rows in seedrows.items():
    r=rows[0];verts=path(r['word']); n=len(verts); local={0,n-1}|{i+k for ch in r['chords'] for i in ch for k in range(-2,3) if 0<=i+k<n};done=set()
    for row in rows:
     fixed=set(row['rm']); rest=[i for i in range(n) if i not in fixed]
     for h in range(len(fixed),4):
      for extra in itertools.combinations(rest,h-len(fixed)):
       if h==3 and len(fixed)==1 and not(local.intersection(extra)):continue
       mask=tuple(sorted(fixed.union(extra)))
       if mask in done:continue
       done.add(mask)
       yield seed,mask,[v for i,v in enumerate(verts) if i not in mask]
if __name__=='__main__':
 with (D/'broader.map').open('w') as mapfile,(D/'broader.results').open('w') as dest:
    p=subprocess.Popen([str(D/'unmasked'),'192','1700000'],stdin=subprocess.PIPE,stdout=dest,text=True)
    for seed,mask,verts in stream():
     try:p.stdin.write('points '+' '.join(map(str,verts))+'\n')
     except BrokenPipeError:break
     print(seed,*mask,file=mapfile)
    p.stdin.close()
    assert p.wait()==0
