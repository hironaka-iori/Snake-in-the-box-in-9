from pathlib import Path
import json,time,argparse
R=Path('E:/Snake-in-a-box');H=R/'milestones/189-middle-replacements'
def neighbours(v):return [v^(1<<k) for k in range(8)]
NB=[neighbours(v) for v in range(256)];MASK=[sum(1<<u for u in ns) for ns in NB];ALL=(1<<256)-1
def verify(path):
    assert len(path)==len(set(path))
    for i,u in enumerate(path):
        for j in range(i+1,len(path)):assert ((u^path[j]).bit_count()==1)==(j==i+1)
def main(maxremoved,seconds):
    row=json.loads((H/'data/replacement-contexts.json').read_text())['rows'][0];p=row['middle'];starttime=time.monotonic();total=0;records=[];found=[];stopped=False
    for removed in range(1,maxremoved+1):
        rec={'removed_block_size':removed,'windows_complete':0,'nodes':0,'solutions':0}
        for i in range(len(p)-removed-1):
            j=i+removed+1;s,t=p[i],p[j];fixed=p[:i]+p[j+1:];retained=fixed+[s,t];forbidden=sum(1<<v for v in retained)
            for v in fixed:forbidden|=MASK[v]
            permitted=ALL&~forbidden;path=[s];localnodes=0;solution=None;complete=True
            def dfs(u,left,used):
                nonlocal localnodes,solution,complete
                localnodes+=1
                if localnodes%4096==0 and time.monotonic()-starttime>seconds:complete=False;return False
                if (u^t).bit_count()>left:return False
                if left==1:
                    if t in NB[u] and not (MASK[t]&(used&~(1<<u))):solution=path+[t];return True
                    return False
                cand=MASK[u]&permitted&~used
                while cand:
                    bit=cand&-cand;cand-=bit;v=bit.bit_length()-1
                    if MASK[v]&(used&~(1<<u)):continue
                    if t in NB[v] and left!=2:continue
                    if (v^t).bit_count()>left-1:continue
                    path.append(v)
                    if dfs(v,left-1,used|bit):return True
                    path.pop()
                    if not complete:return False
                return False
            dfs(s,removed+3,1<<s);rec['nodes']+=localnodes;total+=localnodes
            if not complete:stopped=True;break
            rec['windows_complete']+=1
            if solution:
                q=p[:i]+solution+p[j+1:];verify(q);assert len(q)==98
                found.append({'removed_block_size':removed,'start':i,'end':j,'replacement':solution,'middle_vertices':q});rec['solutions']+=1
        records.append(rec);print(json.dumps(rec),flush=True)
        if stopped:break
    out={'scope':'Retain the entire common95-edgeQ8path outside one contiguous interior block, retain its original endpoint order, and replace the block by a path two edges longer. No externalQ9outer restrictions imposed.','max_removed_requested':maxremoved,'seconds':time.monotonic()-starttime,'time_limit':seconds,'status':'INCOMPLETE' if stopped else 'COMPLETE','nodes':total,'records':records,'solutions':found}
    (H/'data/local-repair.json').write_text(json.dumps(out,indent=2)+'\n');print('TOTAL',out['status'],out['seconds'],total,'solutions',len(found),flush=True)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--max-removed',type=int,default=16);ap.add_argument('--seconds',type=float,default=120);a=ap.parse_args();main(a.max_removed,a.seconds)
