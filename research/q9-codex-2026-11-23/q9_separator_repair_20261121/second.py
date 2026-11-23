import itertools,json,random
from prepare import D,R,NB,words,majority,graph,parts,bridges
from solve import solve
from connect import repair
def obstacle(A):
    adj=graph(A);tip={x for x in A if len(adj[x])==1};branch=sorted(x for x in A if len(adj[x])>=3)
    for k in (1,2,3):
        for ls in itertools.combinations(branch,k):
            C=set(ls);groups=parts(adj,C);need=len(C&tip)+sum(max(len(g&tip),2-min(2,len(set.union(*(adj[x] for x in g))&C))) for g in groups)
            if need>2 or len(groups)>len(C)+1:return C,groups,need
    return None
def main():
    jobs=[json.loads(l)[1] for l in (D/'broadfamilies.jsonl').read_text().splitlines()]
    mosaic=list(map(json.loads,(D/'mosaic_plans.jsonl').read_text().splitlines()))
    base=[(j,jobs[j],set(B)) for j,i,st,B in map(json.loads,(D/'connected_wide.jsonl').read_text().splitlines()) if st=='FOUND']
    base.extend((j,mosaic[j],set(B)) for j,s,st,B in map(json.loads,(D/'mosaic.jsonl').read_text().splitlines()) if st=='FOUND')
    rng=random.Random(335711);done=set();plans=[];found=0
    for j,source,A in base:
        key=tuple(sorted(A))
        if key in done:continue
        done.add(key);ob=obstacle(A)
        if not ob:continue
        C,gs,needed=ob;found+=1;old_m=set(source['qs']);old_fixed=set(source['cut'])|set.union(*(A&NB[q] for q in old_m))
        options=bridges(A,C,gs,rng)
        for kind,(qs,target,rm,add) in options:
            mags=old_m|set(qs);fixed=target|C|old_fixed
            banned=set.union(*(NB[q] for q in mags))-(fixed|add)
            if old_fixed&rm or add&set.union(*(NB[q] for q in old_m)):continue
            if (banned&A)!=rm:continue
            order=sorted(A-fixed-rm);rng.shuffle(order)
            for k in sorted({max(1,len(rm),len(add)),5}):
                if k<len(rm):continue
                drop=sorted(rm|set(order[:35]));new=sorted(x for x in range(512) if x.bit_count()%2==0 and x not in A|banned)
                c=dict(row=source['row'],kind=kind,qs=sorted(mags),ends=sorted(target),cut=sorted(C),remove=sorted(rm),added=sorted(add),drop=drop,new=new,k=k)
                plans.append(dict(A=key,old_cut=source['cut'],new_cut=sorted(C),new_components=len(gs),required=needed,case=c))
        if found>=16:break
    (D/'second_jobs.jsonl').write_text(''.join(json.dumps(p,separators=(',',':'))+'\n' for p in plans))
    for i,rec in enumerate(plans):
        A=set(rec['A']);c=rec['case'];st,_,conf,w=solve(A,c,9500)
        print(json.dumps([i,st,conf,w],separators=(',',':')),flush=True)
        if w:return
if __name__=='__main__':main()
