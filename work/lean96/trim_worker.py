from common import *
from trim import trim
import sys
i=int(sys.argv[1]);proof=Path(sys.argv[2]);dest=Path(sys.argv[3])
data=formula(i);core=trim(data,proof)
tmp=dest.with_suffix('.tmp')
with tmp.open('w',encoding='utf-8') as f:
    json.dump(core,f,separators=(',',':'))
os.replace(tmp,dest)
print(json.dumps(dict(original=len(core['clauses']),derived=len(core['proof']))),flush=True)
