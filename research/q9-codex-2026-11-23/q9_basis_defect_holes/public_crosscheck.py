from collections import Counter
import json,subprocess
from prep import R,D
from run import validate,verify
def main():
 target=192;root=R/'q9_change_basis'
 raw=[l.rstrip().split() for l in (root/'public191.points').open()];status={int(v[1]):v[2] for l in (root/'public_trade12.log').open() if (v:=l.split()) and v[0]=='R'}
 assert len(raw)==len(status)==131 and set(status.values())=={'CLOSED'}
 import sys
 direct='direct' in sys.argv;name='direct' if direct else 'unmasked'
 ids=range(131) if direct else [0,19,47,73,105,130]
 dest=[]
 for i in ids:
    row=raw[i];assert row[0]=='points';q=list(map(int,row[1:]));assert len(q)==192;validate(q)
    lines=['points '+' '.join(map(str,q[:j]+q[j+1:]))+'\n' for j in range(len(q))]
    out=subprocess.run([str(D/name),'192','1700000'],input=''.join(lines),capture_output=True,text=True,check=True).stdout
    (D/f'{name}_public_row_{i}.log').write_text(out)
    result={};hits=[]
    for l in out.splitlines():
     v=l.split()
     if v[0]=='R':result[int(v[1])]=v[2]
     if v[0]=='FOUND':
        j=int(v[1]);hits.append(verify(l,q[:j]+q[j+1:],target))
    assert not hits and len(result)==192 and set(result.values())=={'CLOSED'}
    dest.append(dict(row=i,deletions=len(result),outcomes=dict(Counter(result.values()))));print(dest[-1],flush=True)
 (D/f'{name}_public_crosscheck.json').write_text(json.dumps(dest,indent=2)+'\n')
if __name__=='__main__':main()
