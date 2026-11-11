from pathlib import Path
import json,time
H=Path('E:/Snake-in-a-box/milestones/190-exchange-constraints');p=json.loads((H/'data/middle95.json').read_text())['middle'];NB=[{v^(1<<k) for k in range(8)} for v in range(256)];oldset=set(p)
def connectors(s,t,length,retained):
    forbidden=set(retained)
    for v in retained-{s,t}:forbidden.update(NB[v])
    allowed=set(range(256))-forbidden;path=[s];out=[]
    def dfs(u,left):
        if (u^t).bit_count()>left:return
        if left==1:
            if t in NB[u] and all(t not in NB[v] for v in path[:-1]):out.append(path+[t])
            return
        for v in sorted((NB[u]&allowed)-set(path)):
            if any(v in NB[w] for w in path[:-1]):continue
            if t in NB[v] and left!=2:continue
            path.append(v);dfs(v,left-1);path.pop()
    dfs(s,length);return out
def main():
    start=time.monotonic();positions=0;lengthcases=0;connectorpairs=0;solution=None;complete=True;by_split=[]
    for first_size in range(1,5):
        second_size=5-first_size;count=0
        for i in range(1,95):
            for j in range(i+first_size+1,96-second_size):
                positions+=1;count+=1;deleted=p[i:i+first_size]+p[j:j+second_size];retained=oldset-set(deleted);left=p[:i];centre=p[i+first_size:j];right=p[j+second_size:]
                assert len(retained)==91 and centre and right
                for mid in [centre,centre[::-1]] if len(centre)>1 else [centre]:
                    a,b=left[-1],mid[0];c,d=mid[-1],right[0]
                    for length in range(2,8):
                        other=9-length
                        if (a^b).bit_count()>length or (c^d).bit_count()>other:continue
                        if ((a^b).bit_count()-length)%2 or ((c^d).bit_count()-other)%2:continue
                        lengthcases+=1;first=connectors(a,b,length,retained)
                        if not first:continue
                        second=connectors(c,d,other,retained)
                        for x in first:
                            for y in second:
                                connectorpairs+=1
                                if set(x[1:-1])&set(y[1:-1]):continue
                                if any(v in NB[u] for u in x[1:-1] for v in y[1:-1]):continue
                                q=left+x[1:-1]+mid+y[1:-1]+right
                                assert len(q)==98 and len(set(q))==98
                                assert all(((q[u]^q[v]).bit_count()==1)==(v==u+1) for u in range(98) for v in range(u+1,98))
                                solution={'first_start':i,'second_start':j,'first_size':first_size,'second_size':second_size,'middle_chain_reversed':mid!=centre,'connector_lengths':[length,other],'middle_vertices':q}
                                break
                            if solution:break
                        if solution:break
                    if solution:break
                if solution:break
                if positions%256==0 and time.monotonic()-start>120:complete=False;break
            if solution or not complete:break
        by_split.append({'first_size':first_size,'second_size':second_size,'position_pairs':count});print(json.dumps(by_split[-1]),flush=True)
        if solution or not complete:break
    out={'status':'FEASIBLE' if solution else 'COMPLETE_NO_REPLACEMENT' if complete else 'INCOMPLETE','seconds':time.monotonic()-start,'position_pairs':positions,'connector_length_cases':lengthcases,'connector_pairs':connectorpairs,'by_split':by_split,'scope':'Exactly five omitted internal positions contained in two disjoint intervals, with both possible orders of the retained middle chain. All connector lengths2..7 summing to9. No externalQ9restrictions.','solution':solution}
    (H/'data/two-intervals-five-omissions.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['solution','by_split']},indent=2),flush=True)
if __name__=='__main__':main()
