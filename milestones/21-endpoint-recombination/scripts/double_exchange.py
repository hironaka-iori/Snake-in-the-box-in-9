"""Exact two-interval donor exchanges for the twelve selected alignments."""
import json,time
from pathlib import Path
from exchange import HERE,parents,transforms,check,sha
def run():
    start=time.monotonic();a,b=parents();apos={v:i for i,v in enumerate(a)}
    pre=[0]
    for v in a:pre.append(pre[-1]|1<<v)
    selected=json.loads((HERE/'data/union-search.json').read_text())['selected_alignments']
    closed=[(1<<v)|sum(1<<(v^(1<<k)) for k in range(9)) for v in range(512)]
    rows=[];best=a
    for index,(_,_,q) in enumerate(transforms(b)):
        if index not in selected:continue
        pos={v:i for i,v in enumerate(q)};anchors=[i for i,v in enumerate(a) if v in pos]
        qp=[0];table=[[closed[v] for v in q]]
        for v in q:qp.append(qp[-1]|1<<v)
        span=1
        while 2*span<=len(q):
            last=table[-1];table.append([last[i]|last[i+span] for i in range(len(q)-2*span+1)]);span*=2
        left=[];right=[]
        for ai,i in enumerate(anchors):
            for j in anchors[ai+1:]:
                if j-i<2:continue
                u,w=pos[a[i]],pos[a[j]];lo,hi=sorted((u,w));n=hi-lo-1
                if n<1:continue
                k=n.bit_length()-1;cm=table[k][lo+1]|table[k][hi-(1<<k)]
                bm=qp[hi]^qp[lo+1];deleted=pre[j]^pre[i+1]
                blocked=cm&(pre[i]|(pre[-1]^pre[j+1]))
                rec=(i,j,u,w,hi-lo-(j-i),bm,cm,deleted,blocked)
                if not blocked&pre[i]:left.append(rec)
                if not blocked&(pre[-1]^pre[j+1]):right.append(rec)
        tested=0;valid=[]
        for x in left:
            i,j,u,w,g,bm,cm,deleted,blocked=x
            for y in right:
                k,l,uu,ww,gg,bb,cc,dd,bl=y
                if j>k or g+gg<=0:continue
                tested+=1
                if blocked&~dd or bl&~deleted or cm&bb:continue
                def interior(s,t):
                    p=q[min(s,t)+1:max(s,t)]
                    return p if s<t else p[::-1]
                child=a[:i+1]+interior(u,w)+a[j:k+1]+interior(uu,ww)+a[l:]
                check(child);assert len(child)-1==186+g+gg
                valid.append({'cuts':[[i,j],[k,l]],'donor_cuts':[[u,w],[uu,ww]],'edges':len(child)-1})
                if len(child)>len(best):best=child
        rows.append({'alignment':index,'left_candidates':len(left),'right_candidates':len(right),'positive_pairs':tested,'valid':valid})
        print(json.dumps({'alignment':index,'pairs':tested,'valid':len(valid),'best':len(best)-1}),flush=True)
    data={'script_sha256_lf':sha(Path(__file__)),'rows':rows,'best_path':best,'best_edges':len(best)-1,'seconds':time.monotonic()-start,'scope':'Two recipient intervals with disjoint interiors, replaced by intervals of the same aligned donor; twelve selected alignments only. Includes nonpositive individual gains when the combined gain is positive.'}
    (HERE/'data/double-exchanges.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
if __name__=='__main__':run()
