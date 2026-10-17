from common import *
from trim import trim
import sys
i=int(sys.argv[1]);proof=Path(sys.argv[2]);dest=Path(sys.argv[3])
data=formula(i);core=trim(data,proof)
save(dest,core)
print(json.dumps(dict(original=len(core['clauses']),derived=len(core['proof']))),flush=True)
