"""Add geometry to the complete history model; ambiguous labels use the minimum
over every compatible shape with a checked or pending geometric certificate.
Lean status is recorded separately and must pass before publishing these rules.
"""
from pathlib import Path
import collections,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
np=model.np;start=time.monotonic();SOURCE=ROOT/'milestones/59-extended-share-window/extended'
meta=json.loads((SOURCE/'data/model.json').read_text())
with np.load(SOURCE/'build/graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert hashlib.sha256(a[k].tobytes()).hexdigest()==h
patterns=json.loads((ROOT/'milestones/66-full-model-and-revision/data/pressured-model.json').read_text())['patterns']
old=json.loads((ROOT/'milestones/61-critical-family-share/data/geometry.json').read_text())['patterns']
proof={tuple(r['directions']):r['lower'] for r in old if len(r['directions'])==11 and r['lower']>0}
selected=json.loads((HERE/'data/proof-plan.json').read_text())
for r in selected:proof[tuple(r['directions'])]=max(proof.get(tuple(r['directions']),0),r['lower'])
eid={tuple(w):i for i,w in enumerate(meta['extensions'])};signatures=collections.defaultdict(list)
for w in model.words(11):signatures[tuple(eid[model.canon(w[j:j+9])] for j in range(3))].append(w)
selected_sigs={tuple(eid[model.canon(r['directions'][j:j+9])] for j in range(3)) for r in selected}
added=[];omitted=[]
for sig in sorted(selected_sigs):
    variants=signatures[sig];lo=min(proof.get(w,0) for w in variants)
    row=dict(signature=sig,variants=variants,variant_bounds=[proof.get(w,0) for w in variants],lower=lo)
    if lo:
        entry=dict(row,edge=2000+len(added),caps={},geometric_lower=lo,mode='share')
        added.append(entry);patterns.append(entry)
    else:omitted.append(row)
prefixes=[()]+sorted({tuple(p['signature'][:j]) for p in patterns for j in (1,2)},key=lambda x:(len(x),x));pid={p:i for i,p in enumerate(prefixes)}
N=meta['states'];B=6**5;D=len(meta['extensions']);sid={tuple(w):i for i,w in enumerate(meta['direction_shapes'])}
compatible=[None]+[sid[model.canon(meta['extensions'][p[-1]][1:])] for p in prefixes[1:]]
trans=np.zeros((len(prefixes),D),dtype=np.int16);output={}
for q,prefix in enumerate(prefixes):
    for d in range(D):
        word=prefix+(d,);options=[p for p in prefixes if p and len(p)<=len(word) and word[-len(p):]==p]
        trans[q,d]=pid[max(options,key=len)] if options else 0
        hit=[i for i,p in enumerate(patterns) if len(word)>=3 and word[-3:]==tuple(p['signature'])]
        if hit:output[q,d]=hit
arrays={k:[] for k in ['U','V','weight','source_edge','history']};counts=[]
for q,prefix in enumerate(prefixes):
    ix=np.arange(len(a['U'])) if q==0 else np.flatnonzero(a['U']//B==compatible[q])
    credits=a['share_lower'][ix].copy();reject=np.zeros(len(ix),dtype=bool)
    for d in {d for qq,d in output if qq==q}:
        positions=np.flatnonzero(a['direction'][ix]==d);codes=a['count_code'][ix[positions]]
        for k in output[q,d]:
            p=patterns[k];qualify=np.ones(len(positions),dtype=bool)
            for c,cap in p['caps'].items():qualify&=(codes//6**(5-int(c)))%6+1<=cap
            if p['mode']=='exclusion':reject[positions[qualify]]=True
            else:
                credits[positions]=np.maximum(credits[positions],p['geometric_lower'])
                good=positions[qualify];credits[good]=np.maximum(credits[good],p['lower'])
    keep=~reject;gained=int((credits[keep]>a['share_lower'][ix[keep]]).sum());rejected=int(reject.sum())
    ix=ix[keep];credits=credits[keep];nxt=trans[q,a['direction'][ix]].astype(np.int64)
    src=a['U'][ix] if q==0 else N+(q-1)*B+a['U'][ix]%B
    dst=np.where(nxt==0,a['V'][ix],N+(nxt-1)*B+a['V'][ix]%B)
    for t in np.unique(nxt):
        if t:assert np.all(a['V'][ix[nxt==t]]//B==compatible[t])
    arrays['U'].append(src.astype(np.int32));arrays['V'].append(dst.astype(np.int32))
    arrays['weight'].append((120*a['count'][ix].astype(np.int64)+credits).astype(np.int16))
    arrays['source_edge'].append(ix.astype(np.int32));arrays['history'].append(np.full(len(ix),q,dtype=np.int16))
    counts.append(dict(history=q,retained=len(ix),rejected=rejected,improved=gained))
arrays={k:np.concatenate(v) for k,v in arrays.items()};np.savez_compressed(HERE/'build/full-graph.npz',**arrays)
out=dict(states=N+(len(prefixes)-1)*B,edges=len(arrays['U']),patterns=patterns,prefixes=prefixes,
    compatible_shapes=compatible,added_signatures=len(added),omitted_signatures=omitted,
    multiple_shape_signatures=sum(len(p['variants'])>1 for p in added),history_counts=counts,
    arrays_sha256={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in arrays.items()},seconds=time.monotonic()-start,
    scope='Complete recorded model with stronger geometry. Ambiguous signatures use a proved lower bound for every shape, or receive no new credit. Lean replay and independent reconstruction tracked separately; no global bound.')
(HERE/'data/full-model.json').write_text(json.dumps(out,indent=2)+'\n')
src=(ROOT/'milestones/66-full-model-and-revision/scripts/analyze_terminal.py').read_text()
src=src.replace("else 'terminal'","else 'full'").replace("['terminal','shares','pressured']","['full']")
(HERE/'scripts/analyze_full.py').write_text(src)
print({k:v for k,v in out.items() if k not in ['patterns','prefixes','compatible_shapes','history_counts','arrays_sha256','omitted_signatures']},flush=True)
