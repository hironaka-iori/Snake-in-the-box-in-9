"""No prescribed ports. A symmetry normalization fixes one endpoint and the first step."""
import itertools,json
from pathlib import Path
from pysat.solvers import Cadical195
from pysat.card import CardEnc,EncType
from search_q9_free_221 import search
def add_pair_cuts(cnf,top,minimum=15):
    direction=[]
    for i in range(9):
        bonds=[]
        for u in range(512):
            if u>>i&1:continue
            v=u^(1<<i);top+=1;bonds.append(top)
            cnf.extend([[-top,u+1],[-top,v+1],[top,-u-1,-v-1]])
        direction.append(bonds)
    # A direction needs only the first minimum order statistics.
    # One-sided unary thresholds suffice: each asserted output entails that
    # many real input edges. Conversely true thresholds can all be asserted.
    def merge(a,b):
        nonlocal top
        n=min(minimum,len(a)+len(b))
        z=list(range(top+1,top+n+1));top+=n
        for q in range(1,n+1):
            # If z[q-1] then every split i+j=q-1 has a[i] or b[j] true.
            for i in range(max(0,q-1-len(b)),min(len(a),q-1)+1):
                j=q-1-i
                cnf.append([-z[q-1]]+([a[i]] if i<len(a) else [])+([b[j]] if j<len(b) else []))
        return z
    unary=[]
    for bonds in direction:
        sets=[[u] for u in bonds]
        while len(sets)>1:sets=[merge(a,b) for a,b in zip(sets[::2],sets[1::2])]
        unary.append(sets[0])
    for a,b in itertools.combinations(unary,2):
        for i in range(minimum):cnf.append([a[i],b[minimum-1-i]])
    return top
if __name__=="__main__":search("free",100000,pair_cuts=add_pair_cuts)
