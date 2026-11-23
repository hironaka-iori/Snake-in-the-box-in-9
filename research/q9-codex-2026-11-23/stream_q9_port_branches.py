"""Consume complete rows from a gzip certificate stream while it is still being produced."""
import json,sys,time,zlib
from concurrent.futures import ProcessPoolExecutor
from search_q9_donor_port_branches import job
def rows(name):
    obj=zlib.decompressobj(31);buf=b''
    with open(name,'rb') as inp:
        while not obj.eof:
            part=inp.read(1024*256)
            if not part:
                time.sleep(2);continue
            buf+=obj.decompress(part);lines=buf.split(b'\n');buf=lines.pop()
            for l in lines:yield json.loads(l)
    assert not buf
if __name__=='__main__':
    from collections import deque
    filename,goal,budget=sys.argv[1:4];pending=deque()
    with ProcessPoolExecutor(2) as pool:
        for i,r in enumerate(rows(filename)):
            pending.append(pool.submit(job,(i,r,int(goal),int(budget))))
            while len(pending)>=4 or pending and pending[0].done():
                v=pending.popleft().result();print(json.dumps(v,separators=(',',':')),flush=True)
                if v[-1]:sys.exit(0)
        for f in pending:
            v=f.result();print(json.dumps(v,separators=(',',':')),flush=True)
            if v[-1]:break
