"""Refine unresolved fixed-facet port cases with 4-dimensional faces and search again."""
import gzip,json,random,sys
from concurrent.futures import ProcessPoolExecutor
from strengthen_q9_donor_port_bounds import strong
from search_q9_donor_port_branches import branch
def worker(task):
    i,r,goal,cap=task
    i,t=strong((i,r,4,591373))
    if 'empty' in t:return i,'EMPTY',0,None,t
    return i,*branch(t,goal,cap),t
if __name__=='__main__':
    src,states,out,limit,cap,work=sys.argv[1:]
    todo={i for i,s,n,w in (json.loads(l) for l in open(states)) if s=='UNKNOWN'}
    ids=sorted(todo);random.Random(749853).shuffle(ids)
    ids=ids[:int(limit)];data={}
    from stream_q9_port_branches import rows
    for i,t in enumerate(rows(src)):
        if i in todo:data[i]=t
        if all(x in data for x in ids):break
    with ProcessPoolExecutor(int(work)) as pool,gzip.open(out,'wt') as f:
        for i,s,n,w,t in pool.map(worker,[(j,data[j],192,int(cap)) for j in ids]):
            f.write(json.dumps([i,t],separators=(',',':'))+'\n');f.flush()
            print(json.dumps([i,s,n,w,t.get('bound')],separators=(',',':')),flush=True)
            if w:break

