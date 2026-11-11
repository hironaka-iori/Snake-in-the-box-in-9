from pathlib import Path
import json,time,itertools
H=Path('E:/Snake-in-a-box/milestones/189-middle-replacements');rows=json.loads((H/'data/replacement-contexts.json').read_text())['rows'];p=rows[0]['middle'];NB=[{v^(1<<k) for k in range(8)} for v in range(256)]
def check(q,n):
    assert len(q)==len(set(q)) and all(0<=v<1<<n for v in q)
    assert all(((q[i]^q[j]).bit_count()==1)==(j==i+1) for i in range(len(q)) for j in range(i+1,len(q)))
def connectors(s,t,length,retained):
    forbidden=set(retained)
    for v in retained-{s,t}:forbidden.update(NB[v])
    allowed=set(range(256))-forbidden;path=[s];out=[]
    def dfs(u,left):
        if (u^t).bit_count()>left:return
        if left==1:
            if t in NB[u] and all(t not in NB[v] for v in path[:-1]):out.append(path+[t])
            return
        for v in sorted(NB[u]&allowed-set(path)):
            if any(v in NB[w] for w in path[:-1]):continue
            if t in NB[v] and left!=2:continue
            path.append(v);dfs(v,left-1);path.pop()
    dfs(s,length);return out
start=time.monotonic();cases=0;pairs=0;connectorpairs=0;solutions=[];retained_all=set(p)
for i in range(1,95):
    for j in range(i+2,95):
        pairs+=1;retained=retained_all-{p[i],p[j]}
        left=p[:i];centre=p[i+1:j];right=p[j+1:]
        for mid in [centre,centre[::-1]] if len(centre)>1 else [centre]:
            a,b=left[-1],mid[0];c,d=mid[-1],right[0]
            for length in [2,3,4]:
                other=6-length
                if (a^b).bit_count()>length or (c^d).bit_count()>other:continue
                if ((a^b).bit_count()-length)%2 or ((c^d).bit_count()-other)%2:continue
                cases+=1;first=connectors(a,b,length,retained);second=connectors(c,d,other,retained)
                for x in first:
                    for y in second:
                        connectorpairs+=1
                        if set(x[1:-1])&set(y[1:-1]):continue
                        if any(v in NB[u] for u in x[1:-1] for v in y[1:-1]):continue
                        q=left+x[1:-1]+mid+y[1:-1]+right;check(q,8);assert len(q)==98
                        solutions.append({'removed_positions':[i,j],'middle_chain_reversed':mid!=centre,'connector_lengths':[length,other],'middle_vertices':q})
out={'status':'COMPLETE','scope':'All two nonadjacent internal positions in the common95-edge middle path, both orders of the retained middle chain, and every possible pair of induced connectors totalling six edges. No externalQ9constraints. Adjacent removals and single removals are covered by the separate contiguous-block search.','pairs':pairs,'connector_length_cases':cases,'connector_pairs':connectorpairs,'seconds':time.monotonic()-start,'solutions':solutions}
(H/'data/two-changes.json').write_text(json.dumps(out,indent=2)+'\n');(H/'scripts/two_changes.py').write_bytes(Path(__file__).read_bytes());print(json.dumps({k:v for k,v in out.items() if k!='solutions'},indent=2));print('SOLUTIONS',len(solutions))
