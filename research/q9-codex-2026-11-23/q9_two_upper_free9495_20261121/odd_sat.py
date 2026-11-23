import os,sys
from banks import path
from sat import search,R,W
os.environ['Q9_NO_PINS']='1';os.environ['Q9_EXPORT_PROOF']='1'
for i in map(int,sys.argv[1:]):
    _,_,_,_,a,b=R[str(i)];search(i,-1,191,320000,(path(a),path(b,path(W[i])[-1])))
