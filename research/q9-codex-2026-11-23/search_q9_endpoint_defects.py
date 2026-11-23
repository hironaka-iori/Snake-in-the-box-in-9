import json,sys
from pathlib import Path
bank=json.loads(Path(sys.argv[1]).read_text())
def optimum(target):
    best=999
    witness=None
    for idx,row in enumerate(bank):
        p=row['vertex_sequence']; n=len(p)
        adj=[0]*512; used=set(p)
        for x in p:
            for i in range(9):adj[x^(1<<i)]+=1
        front=[];back=[]
        def dfs(left,right,cost):
            nonlocal best,witness
            if cost>=best:return
            if left+right==0:
                best=cost;witness=(idx,front[::-1]+p+back);return
            seq=front if left else back
            u=seq[-1] if seq else (p[0] if left else p[-1])
            for i in range(9):
                v=u^(1<<i)
                if v in used:continue
                z=cost+adj[v]-1
                if z>=best:continue
                used.add(v);seq.append(v)
                for j in range(9):adj[v^(1<<j)]+=1
                dfs(left-1 if left else 0,right if left else right-1,z)
                for j in range(9):adj[v^(1<<j)]-=1
                seq.pop();used.remove(v)
        for left in range(target-190):dfs(left,target-191-left,0)
    idx,p=witness
    assert len(p)==len(set(p))==target+1 and all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
    chords=[(i,j) for j in range(len(p)) for i in range(j-1) if (p[i]^p[j]).bit_count()==1]
    assert len(chords)==best
    return dict(edges=target,chords=chords,bank_index=idx,vertices=p)
print(json.dumps([optimum(t) for t in range(192,197)]))
