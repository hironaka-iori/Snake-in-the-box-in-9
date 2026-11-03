"""Keep only the eight-cycle containing the fixed six-transition window."""
from pathlib import Path
import hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.dont_write_bytecode=True
sys.path[:0]=[str(R/'work/share_packages'),str(R/'milestones/10-window-aggregate/scripts')]
from gen_lean_sat import TaggedEncoding
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
folder=H/'work/closure';folder.mkdir(exist_ok=True);assert not any(folder.iterdir())
meta=json.loads((H/'work/short/encoding.json').read_text())
enc=TaggedEncoding(meta['window'],meta['bounds'],radius=9)
raw=lambda:(f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode('ascii')
assert raw()==(H/'work/short/base.cnf').read_bytes()
cycle=[0,1,3,7,8,12,14,15]
assert len(set(cycle))==8 and all(sum((v^w).bit_count()==1 for w in cycle)==2 for v in cycle)
enc.add([-enc.var[v] for v in cycle],('cut',))
(folder/'base.cnf').write_bytes(raw())
meta.update(label='closure',status='PREPARED_NOT_RUN',clauses=len(enc.clauses),cnf_sha256=sha(folder/'base.cnf'),
 additional_cycle_cuts=[cycle],scope='The short upper-cap input plus one necessary eight-cycle exclusion, with no endpoint restriction.')
meta['source_files_sha256'].update({Path(__file__).relative_to(R).as_posix():sha(Path(__file__)),
 (H/'work/short/encoding.json').relative_to(R).as_posix():sha(H/'work/short/encoding.json')})
(folder/'encoding.json').write_text(json.dumps(meta,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:meta[k] for k in ['label','clauses','variables','additional_cycle_cuts','cnf_sha256']}))
