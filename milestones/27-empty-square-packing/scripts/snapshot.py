"""Pin the collaborator inputs without checking out or modifying that branch."""
import hashlib,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
def git(*args):
    return subprocess.check_output(['git','-c',f'safe.directory={ROOT.as_posix()}',*args],cwd=ROOT)
ref=git('rev-parse','fcf168386b4797e90a2553d8996b84120bf0294f').decode().strip()
names=['work/spectral/ShareCharge.lean','milestones/11-local-ceiling/s0_corner_charge.md','milestones/11-local-ceiling/s0_lean_design.md']
prefix='milestones/11-local-ceiling/s0_radius4/'
names += [prefix+n for n in ['README.md','aut_base.json','aut_pair_lo.json','aut_single_lo.json','aut_single_ub.json','aut_tri_lo.json','threshold_results.jsonl','ceiling_results.jsonl','probe_results.jsonl','refshare_results.jsonl','windows_results.jsonl','e1lib.py','refine_share.py']]
rows=[]
for name in names:
    original=git('show',f'{ref}:{name}')
    data=original.replace(b'\r\n',b'\n')
    dest=HERE/'upstream'/Path(name).name
    dest.write_bytes(data)
    rows.append(dict(source=name,saved=str(dest.relative_to(HERE)),source_blob_sha256=hashlib.sha256(original).hexdigest(),sha256_lf=hashlib.sha256(data).hexdigest()))
(HERE/'data/provenance.json').write_text(json.dumps(dict(branch='research/unconditional-241',commit=ref,files=rows),indent=2)+'\n')
print(ref,len(rows),'files')
