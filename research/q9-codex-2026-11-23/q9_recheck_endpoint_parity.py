"""Recheck endpoint extensions in their stored orientation with relative parity."""
import json
from search_q9_flexible_corners import solve
for line in open("q9_flexible_endpoint_add_192.jsonl"):
    _,key,offset,count,_=json.loads(line)
    q=bytes.fromhex(key)
    ids=list(range(offset,len(q),2))
    assert len(ids)==count
    status,w=solve(q,[],ids,192,3500,True)
    print(json.dumps([status,key,offset,count,w]),flush=True)
    if w:break
