"""Fix a two-component Q8 forest and search a free chordless path joining its ports in the opposite layer."""
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations,product
import gzip,json,random,sys
from certify_q9_intact_q8_facet import build
from search_q9_donor_port_branches import branch
def jobs(filename,goal):
    tasks={}
    for line in open(filename):
        xs=list(map(int,line.split()));a=xs[1:1+xs[0]];b=xs[2+xs[0]:];assert len(b)==xs[1+xs[0]]
        low=set(a+b);assert 0 in low and len(low)==len(a)+len(b)
        if len(low)<96:continue
        for arm in [a,b]:
            assert all((x^arm[j]).bit_count()==1 if j==i+1 else (x^arm[j]).bit_count()>1 for i,x in enumerate(arm) for j in range(i+1,len(arm)))
        assert all((x^y).bit_count()>1 for x in a for y in b)
        for i,j in product((0,-1),repeat=2):
            ports=sorted([a[i],b[j]])
            ends=[a[-1-i],b[-1-j]];even=sum(x.bit_count()%2==0 for x in ends);full=[even,2-even]
            delta=sum((-1)**x.bit_count() for x in low)-(full[0]-full[1])//2
            key=tuple(sorted(low)),tuple(ports),tuple(full)
            tasks[key]=(sorted(low),ports,full,delta)
    items=list(tasks.values());random.Random(839).shuffle(items);items.sort(key=lambda v:-len(v[0]));return items
def work(t):
    idx,rec,goal,cap=t;low,ports,full,delta=rec
    axes=list(combinations(range(8),3));random.Random(403215).shuffle(axes)
    result=build([0],ports,low,[0,0],delta,axes[:10])
    if not result:return [idx,'EMPTY',0,None,None]
    fee,scale,groups,c=result;num=fee+sum(g[0][2] for _,g in groups);u=len(low)-1+num//scale;u-=int(u%2!=full[0]%2)
    record=dict(word='',added=sorted(set(low)-{0}),ports=ports,full=full,ends=[0,0],delta=delta,numerator=num,bound=u,cert=c)
    state,n,w=branch(record,goal,cap);return [idx,state,n,w,record]
if __name__=='__main__':
    src,goal,cap,lim,workers,out=sys.argv[1:];todo=jobs(src,int(goal))[:int(lim)]
    print('START',len(todo),flush=True)
    with ProcessPoolExecutor(int(workers)) as pool,gzip.open(out,'wt') as f:
        for i,s,n,w,r in pool.map(work,[(i,x,int(goal),int(cap)) for i,x in enumerate(todo)]):
            f.write(json.dumps(r,separators=(',',':'))+'\n');f.flush();print(json.dumps([i,s,n,w,None if not r else r['bound']],separators=(',',':')),flush=True)
            if w:break

