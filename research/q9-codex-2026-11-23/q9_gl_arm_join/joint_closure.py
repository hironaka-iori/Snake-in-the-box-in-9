from pathlib import Path
import json,subprocess
D=Path(__file__).resolve().parent
old=(D/'closure.txt').read_text().splitlines()
words=[l.split()[0] for l in old];seen=set(words);ref={}
def two(rows,parent):
    new=set()
    for line in rows:
        w,i,a,b,g,h=line.split()
        if w not in seen:new.add(w);ref[w]=[parent[int(i)],'basis',int(a),int(b),int(g),int(h)];seen.add(w)
    return new
front=two((D/'two_new.txt').read_text().splitlines(),words);history=[];roundno=0
while front and len(seen)<20000:
    roundno+=1;batch=sorted(front);content='\n'.join(batch)+'\n'
    p=subprocess.run([D/'transform','9'],input=content,capture_output=True,text=True,check=True);nexts=set()
    for line in p.stdout.splitlines():
        w,i,u,v,orig=line.split()
        if w not in seen:seen.add(w);nexts.add(w);ref[w]=[batch[int(i)],'rank1',int(u),int(v)]
    t=subprocess.run([D/'two_basis'],input=''.join(w+' 0 0 0 0\n' for w in batch),capture_output=True,text=True,check=True)
    more=two(t.stdout.splitlines(),batch);history.append([len(batch),len(nexts),len(more),p.stderr.strip().splitlines()[-1],t.stderr.strip()]);front=nexts|more
(D/'joint_lineage.json').write_text(json.dumps(ref))
(D/'joint.txt').write_text('\n'.join(sorted(old+[w+' -2 1 1 0' for w in ref]))+'\n')
(D/'joint_stats.json').write_text(json.dumps(dict(added=len(ref),waves=history,pending=len(front),total=len(seen))))
print('total',len(seen),'waves',history,'pending',len(front))
