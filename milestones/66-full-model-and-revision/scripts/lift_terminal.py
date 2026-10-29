"""Add exact pattern history for the milestone-65 terminal count theorem.

This is a finite-model computation. The source model still has inherited
numerical premises and an incomplete arbitrary-snake assembly.
"""
from pathlib import Path
import hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
np=model.np;start=time.monotonic()
for d in ['build','data','logs']:(HERE/d).mkdir(parents=True,exist_ok=True)
SOURCE=ROOT/'milestones/59-extended-share-window/extended'
meta=json.loads((SOURCE/'data/model.json').read_text())
with np.load(SOURCE/'build/graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert hashlib.sha256(a[k].tobytes()).hexdigest()==h
target=(0,1,2,3,0,4,3,2,5,4,3)
sequence=[model.canon(target[j:j+9]) for j in range(3)]
extension_id={tuple(w):i for i,w in enumerate(meta['extensions'])}
pattern=[extension_id[w] for w in sequence]
assert len(set(pattern))==3
# Exhaust every induced 11-direction word over at most nine coordinates.
# Three overlapping canonical 9-windows must identify exactly this pattern.
matching=[];tested=0
for w in model.words(11):
    tested+=1
    if [model.canon(w[j:j+9]) for j in range(3)]==sequence:matching.append(w)
assert matching==[target],matching
N=meta['states'];B=6**5
shape_id={tuple(w):i for i,w in enumerate(meta['direction_shapes'])}
compatible=[None]+[shape_id[model.canon(sequence[q-1][1:])] for q in (1,2)]
def advance(q,s):
    if q==1 and s==pattern[1]:return 2
    return 1 if s==pattern[0] else 0
arrays={k:[] for k in ['U','V','weight','source_edge','history']};removed=[]
for q in range(3):
    ix=np.arange(len(a['U'])) if q==0 else np.flatnonzero(a['U']//B==compatible[q])
    reject=(a['direction'][ix]==pattern[2])&(a['count'][ix]<=2) if q==2 else np.zeros(len(ix),dtype=bool)
    removed.extend(ix[reject].tolist());ix=ix[~reject]
    src=a['U'][ix] if q==0 else N+(q-1)*B+a['U'][ix]%B
    nxt=np.where(a['direction'][ix]==pattern[0],1,0)
    if q==1:nxt=np.where(a['direction'][ix]==pattern[1],2,nxt)
    dst=np.where(nxt==0,a['V'][ix],N+(nxt-1)*B+a['V'][ix]%B)
    for t in (1,2):assert np.all(a['V'][ix[nxt==t]]//B==compatible[t])
    arrays['U'].append(src.astype(np.int32));arrays['V'].append(dst.astype(np.int32))
    arrays['weight'].append((120*a['count'][ix].astype(np.int64)+a['share_lower'][ix]).astype(np.int16))
    arrays['source_edge'].append(ix.astype(np.int32));arrays['history'].append(np.full(len(ix),q,dtype=np.int8))
    print('History',q,'retained',len(ix),'rejected',int(reject.sum()),flush=True)
arrays={k:np.concatenate(v) for k,v in arrays.items()}
np.savez_compressed(HERE/'build/terminal-graph.npz',**arrays)
out=dict(states=N+2*B,edges=len(arrays['U']),source_states=N,source_edges=len(a['U']),
    added_states=2*B,pattern=target,pattern_ids=pattern,compatible_shapes=compatible,
    canonical_eleven_shapes_tested=tested,matching_shapes=matching,rejected_transitions=len(removed),
    removed_source_edges=removed,seconds=time.monotonic()-start,
    source_arrays_sha256=meta['arrays_sha256'],
    arrays_sha256={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in arrays.items()},
    scope='Complete lift of the recorded source model, with a Lean-checked geometric exclusion. History recognition and inherited source premises still need proof assembly; no global bound.')
(HERE/'data/terminal-model.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['removed_source_edges','source_arrays_sha256','arrays_sha256']},flush=True)
