"""Find 191-edge intermediates outside the published bank and check extensions."""
import gzip,json,sys
from search_q9_flexible_columns import complete
from verify_q9_center_avoidance import code,verify
def key(p):return code([v^w for v,w in zip(p,p[1:])])
public={key(list(map(int,s.split()))) for s in gzip.open('q9_port_followup_public191.txt.gz','rt')}
assert len(public)==131
for row in map(json.loads,open(sys.argv[1])):
    if row[0]=='control':continue
    m=int(row[-3],16);h={x for x in range(512) if m>>x&1}
    c=row[4];S={x%256 for x in h};patch={x for x in range(256) if x.bit_count()%2!=c};known=[]
    def reject(p):
        if len(p)==192 and key(p) in public:
            known.append(1);return True
        return False
    st,w=complete(h,S,patch,191,int(sys.argv[2]),0,S,c,reject)
    if w:
        verify(w);assert len(w)>=192 and key(w) not in public
        for v in (w[0],w[-1]):
            for d in range(9):
                z=v^(1<<d)
                if z not in w and sum((x^z).bit_count()==1 for x in w)==1:
                    w=[z]+w if v==w[0] else w+[z];break
        verify(w)
    print(json.dumps([row[-3],st,len(known),w],separators=(',',':')),flush=True)
    if w:break
