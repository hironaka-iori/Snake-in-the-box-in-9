"""Measure exact sharing of accepted count sets for the next finite certificate.
This is a data representation check, not a proof of retention coverage.
"""
from pathlib import Path
import collections,gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
start=time.monotonic();graph=ROOT/'milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz'
meta=json.loads((graph.parent.parent/'data/source-proved-model.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
with np.load(graph) as z:
    d=z['direction'];q=z['history'];c=z['count_code']
for name,a in [('direction',d),('history',q),('count_code',c)]:assert sha(a.tobytes())==meta['arrays_sha256'][name]
b=75*d+q;offset=np.r_[0,np.cumsum(np.bincount(b,minlength=37875))]
del d,q,b
mask_ids={};mask_codes=[];blocks=[]
for block in range(37875):
    codes=c[offset[block]:offset[block+1]]
    if len(codes)==0:continue
    raw=codes.tobytes()
    if raw not in mask_ids:mask_ids[raw]=len(mask_codes);mask_codes.append(codes.copy())
    blocks.append([block,mask_ids[raw]])
# The two terminal IDs denote constant false/true on the remaining suffix.
# Nonterminals record their remaining digit count, so no variable is dropped.
nodes=[];intern={}
def build(mask,depth):
    if not mask.any():return 0
    if mask.all():return 1
    assert depth>0
    children=tuple(build(part,depth-1) for part in np.split(mask,6))
    key=(depth,children)
    if key not in intern:
        intern[key]=len(nodes)+2;nodes.append([depth,*children])
    return intern[key]
def expand(node,depth):
    if node<2:return np.full(6**depth,node==1,dtype=bool)
    row=nodes[node-2];assert row[0]==depth
    return np.concatenate([expand(child,depth-1) for child in row[1:]])
roots=[];runs=[]
for codes in mask_codes:
    mask=np.zeros(46656,dtype=bool);mask[codes]=True
    root=build(mask,6);roots.append(root)
    assert np.array_equal(np.flatnonzero(expand(root,6)),codes)
    runs.append(int(1+np.count_nonzero(codes[1:]!=codes[:-1]+1)))
for block,mi in blocks:assert np.array_equal(c[offset[block]:offset[block+1]],mask_codes[mi])
# A second decoder follows integer base-six digits rather than expanding lists.
table=np.asarray(nodes,dtype=np.int32);all_codes=np.arange(46656,dtype=np.int32)
for root,codes in zip(roots,mask_codes):
    current=np.full(46656,root,dtype=np.int32)
    for depth in range(6,0,-1):
        active=current>=2;node=current[active]-2
        assert np.all(table[node,0]==depth)
        digit=all_codes[active]//(6**(depth-1))%6
        current[active]=table[node,digit+1]
    assert np.all(current<2)
    assert np.array_equal(np.flatnonzero(current==1),codes)
payload=dict(format='Ordered six-digit radix-six decision DAG; terminal0=false terminal1=true',
    nodes=nodes,roots=roots,blocks=blocks,source_arrays_sha256={k:meta['arrays_sha256'][k] for k in ['direction','history','count_code']})
raw=json.dumps(payload,separators=(',',':')).encode();compressed=gzip.compress(raw,mtime=0)
out=HERE/'data/coverage-membership-dag.json.gz';out.write_bytes(compressed)
report=dict(status='PASS_EXACT_MEMBERSHIP_DAG_ROUNDTRIP',scope='Exact representation of saved accepted code sets only. This does not prove numericKeep coverage or any exclusion theorem.',
    compatible_blocks=len(blocks),unique_code_sets=len(mask_codes),nonterminal_nodes=len(nodes),terminals=2,
    nodes_by_remaining_digits=dict(sorted(collections.Counter(row[0] for row in nodes).items())),
    interval_runs_per_unique_set=dict(min=min(runs),max=max(runs),total=sum(runs)),
    independently_expanded_sets=len(roots),all_block_lists_matched=True,
    integer_digit_decoder_checks=len(roots)*46656,integer_digit_decoder_matches=True,
    raw_payload_bytes=len(raw),compressed_payload_bytes=len(compressed),compressed_sha256=sha(compressed),
    source_arrays_sha256=payload['source_arrays_sha256'],script_sha256=sha(Path(__file__).read_bytes()),seconds=time.monotonic()-start)
(HERE/'data/coverage-profile.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
