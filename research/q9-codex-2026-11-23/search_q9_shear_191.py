"""Seek previously unseen record-length intermediates among the harder sheared halves."""
import gzip,json
from search_q9_checkerboard_walk import half_completion,shape
from verify_q9_center_avoidance import verify
base={}
for line in open('q9_projected_checkerboard_sets.txt'):
    i,_,*xs=map(int,line.split());base[i]=set(xs)
known={shape(list(map(int,line.split()))) for line in gzip.open('q9_port_followup_public191.txt.gz','rt')}
for row in map(json.loads,open('q9_checkerboard_shears_retry.jsonl')):
    i,t,m,b=row[:4];A={x^t if ((x&m).bit_count()%2)^b else x for x in base[i]}
    rejected=[]
    def old(p):
        if len(p)==192 and shape(p) in known:
            rejected.append(1);return True
        return False
    st,w=half_completion(A,191,35000,A,old)
    if w:
        verify(w)
        for rev in (False,True):
            if rev:w.reverse()
            for d in range(9):
                v=w[-1]^(1<<d)
                if v not in w and sum((x^v).bit_count()==1 for x in w)==1:
                    w.append(v);break
        verify(w)
    print(json.dumps([i,t,m,b,st,len(rejected),w],separators=(',',':')),flush=True)
    if w:break
