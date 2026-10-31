"""Verify all downloaded critical records against the pinned frozen potential."""
from pathlib import Path
import json,gzip,array,hashlib,sys
H=Path(__file__).resolve().parent;D=json.loads((H.parent/'global-cycle-compression-20261031/critical_edges_frozen.json').read_text());raw=gzip.decompress((H/'frozen_potential.i64.gz').read_bytes());meta=json.loads((H/'frozen_source_analysis.json').read_text());assert hashlib.sha256(raw).hexdigest()==meta['potential_sha256'];pi=array.array('q');pi.frombytes(raw)
if sys.byteorder!='little':pi.byteswap()
assert len(pi)==1601856
assert all(0<=e['u']<len(pi) and 0<=e['v']<len(pi) and e['weight']+pi[e['u']]-pi[e['v']]==480 for e in D)
r={'status':'PASS','potential_values':len(pi),'raw_potential_sha256':hashlib.sha256(raw).hexdigest(),'tight_edges_checked':len(D),'scope':'checks all recorded frozen edges tight; not absent edges or extraction completeness'};(H/'tight_edge_verification.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
