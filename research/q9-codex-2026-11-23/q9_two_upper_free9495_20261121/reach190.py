import os
from banks import path
from sat import search,W,R
os.environ['Q9_NO_PINS']='1';os.environ['Q9_EXPORT_PROOF']='1'
for i in (14,15):
    _,_,_,_,a,b=R[str(i)]
    for c in (0,1):search(i,c,190,180000,(path(a),path(b,path(W[i])[-1])))
