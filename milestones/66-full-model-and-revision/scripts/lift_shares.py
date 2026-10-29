"""Sparse prefix automaton for ten checked eleven-direction patterns."""
from pathlib import Path
import hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
np=model.np;start=time.monotonic();SOURCE=ROOT/'milestones/59-extended-share-window/extended'
name='pressured' if '--new-counts' in sys.argv else 'shares'
meta=json.loads((SOURCE/'data/model.json').read_text())
with np.load(SOURCE/'build/graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert hashlib.sha256(a[k].tobytes()).hexdigest()==h
base=json.loads((ROOT/'milestones/64-neighbour-choice-share/data/choices.json').read_text())['rows']
pack=json.loads((ROOT/'milestones/65-count-saturation-share/data/compact-certificates.json').read_text())['rows']
extension_id={tuple(w):i for i,w in enumerate(meta['extensions'])}
patterns=[]
for row in pack:
    i=row['edge'];case=json.loads((ROOT/f'milestones/65-count-saturation-share/data/cases/e{i:03d}.json').read_text())
    used=set()
    for br in row['certificates']:
        if 'condition' in br['ending']:used.add(br['ending']['condition'])
        used.update(t['condition'] for t in br['steps'] if 'condition' in t)
    ds=tuple(case['directions']);sig=tuple(extension_id[model.canon(ds[j:j+9])] for j in range(3))
    patterns.append(dict(edge=i,directions=ds,signature=sig,caps={k:case['constraints'][k]['hi'] for k in used},
        lower=row['lower'],geometric_lower=base[i]['lower'],mode=row['mode']))
if name=='pressured':
    audit=json.loads((HERE/'data/count-lean-audit.json').read_text());assert audit['status']=='PASS'
    for row in json.loads((HERE/'data/new-count-certificates.json').read_text()):
        ds=tuple(row['directions']);sig=tuple(extension_id[model.canon(ds[j:j+9])] for j in range(3))
        patterns.append(dict(edge=1000+row['phase'],directions=ds,signature=sig,caps={row['position']-5:2},
            lower=0,geometric_lower=0,mode='exclusion'))
# Reject ambiguous recognition; no stronger identification is assumed.
matches={p['signature']:[] for p in patterns};tested=0
for word in model.words(11):
    tested+=1;sig=tuple(extension_id[model.canon(word[j:j+9])] for j in range(3))
    if sig in matches:matches[sig].append(word)
ambiguous=[dict(p,matching_directions=matches[p['signature']]) for p in patterns if matches[p['signature']]!=[p['directions']]]
patterns=[p for p in patterns if matches[p['signature']]==[p['directions']]]
assert all(p['edge']!=24 for p in ambiguous)
print('Ambiguous patterns omitted pending stronger recognition:',[p['edge'] for p in ambiguous],flush=True)
prefixes=[()]+sorted({p['signature'][:j] for p in patterns for j in (1,2)},key=lambda x:(len(x),x))
pid={p:i for i,p in enumerate(prefixes)};N=meta['states'];B=6**5;D=len(meta['extensions'])
shape_id={tuple(w):i for i,w in enumerate(meta['direction_shapes'])}
compatible=[None]+[shape_id[model.canon(meta['extensions'][p[-1]][1:])] for p in prefixes[1:]]
trans=np.zeros((len(prefixes),D),dtype=np.int16);output={}
for q,prefix in enumerate(prefixes):
    for d in range(D):
        word=prefix+(d,);options=[p for p in prefixes if p and len(p)<=len(word) and word[-len(p):]==p]
        trans[q,d]=pid[max(options,key=len)] if options else 0
        hit=[i for i,p in enumerate(patterns) if len(word)>=3 and word[-3:]==p['signature']]
        if hit:output[q,d]=hit
arrays={k:[] for k in ['U','V','weight','source_edge','history']};records=[]
for q,prefix in enumerate(prefixes):
    ix=np.arange(len(a['U'])) if q==0 else np.flatnonzero(a['U']//B==compatible[q])
    credits=a['share_lower'][ix].copy();reject=np.zeros(len(ix),dtype=bool);gained=0
    for d in set(d for qq,d in output if qq==q):
        positions=np.flatnonzero(a['direction'][ix]==d)
        codes=a['count_code'][ix[positions]]
        for k in output[q,d]:
            p=patterns[k];qualify=np.ones(len(positions),dtype=bool)
            for c,cap in p['caps'].items():qualify&=(codes//(6**(5-c)))%6+1<=cap
            if p['mode']=='exclusion':reject[positions[qualify]]=True
            else:
                credits[positions]=np.maximum(credits[positions],p['geometric_lower'])
                good=positions[qualify];credits[good]=np.maximum(credits[good],p['lower'])
    keep=~reject;gained=int((credits[keep]>a['share_lower'][ix[keep]]).sum())
    rejected=int(reject.sum());ix=ix[keep];credits=credits[keep]
    src=a['U'][ix] if q==0 else N+(q-1)*B+a['U'][ix]%B
    nxt=trans[q,a['direction'][ix]]
    # Cast before multiplying: history identifiers use int16, state offsets do not.
    dst=np.where(nxt==0,a['V'][ix],N+(nxt.astype(np.int64)-1)*B+a['V'][ix]%B)
    for t in np.unique(nxt):
        if t:assert np.all(a['V'][ix[nxt==t]]//B==compatible[t])
    arrays['U'].append(src.astype(np.int32));arrays['V'].append(dst.astype(np.int32))
    arrays['weight'].append((120*a['count'][ix].astype(np.int64)+credits).astype(np.int16))
    arrays['source_edge'].append(ix.astype(np.int32));arrays['history'].append(np.full(len(ix),q,dtype=np.int16))
    records.append(dict(history=q,retained=len(ix),rejected=rejected,improved=gained))
    print(records[-1],flush=True)
arrays={k:np.concatenate(v) for k,v in arrays.items()}
np.savez_compressed(HERE/f'build/{name}-graph.npz',**arrays)
out=dict(states=N+(len(prefixes)-1)*B,edges=len(arrays['U']),source_states=N,source_edges=len(a['U']),
    patterns=patterns,ambiguous_patterns=ambiguous,prefixes=prefixes,compatible_shapes=compatible,recognition_tested=tested,
    transitions=trans.tolist(),history_counts=records,seconds=time.monotonic()-start,
    arrays_sha256={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in arrays.items()},
    scope='Complete recorded model with all unambiguously recognized selected local patterns. Ambiguous patterns are omitted; Lean history and inherited model assembly remain unfinished.')
(HERE/f'data/{name}-model.json').write_text(json.dumps(out,indent=2)+'\n')
print('States',out['states'],'edges',out['edges'],'prefix states',len(prefixes),'seconds',out['seconds'],flush=True)
