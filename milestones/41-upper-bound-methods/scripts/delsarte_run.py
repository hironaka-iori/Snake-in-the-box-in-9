import sys; import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '22-global-arguments', 'scripts'))
from delsarte import maxv
for n in (6,7,8,9):
    r={}
    r['delsarte']=maxv(n,use_s0=False)
    r['del+s0']=maxv(n)
    r['del+s0+T>=v']=maxv(n,mu=1)
    print(n,{k:(v-1 if v else None) for k,v in r.items()},flush=True)
