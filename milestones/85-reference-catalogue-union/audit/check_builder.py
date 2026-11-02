"""Compare every isolated reference-filter test with the generated Lean keys."""
from pathlib import Path
import ast,collections,gzip,hashlib,json,re,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic();builder=ROOT/'milestones/70-proof-supported-share-model/scripts/build.py'
tree=ast.parse(builder.read_text());loops=[n for n in ast.walk(tree) if isinstance(n,ast.For) and isinstance(n.target,ast.Name) and n.target.id=='width']
assert len(loops)==1
loop=compile(ast.fix_missing_locations(ast.Module(body=loops,type_ignores=[])),str(builder),'exec')
def canon(w):
    seen=list(dict.fromkeys(w));return tuple(seen.index(x) for x in w)
def encode(c):
    acc=0
    for x in c:acc=6*acc+x-1
    return acc
key235=ROOT/'milestones/54-share-coverage/data/keys_235.json'
key236=ROOT/'milestones/39-audited-bound-236/data/exclusion-catalogue.json'
raw=[(w,[lo for lo,hi in bs]) for w,bs in read(key235)['keys']]+read(key236)
keys=sorted({min((canon(w),tuple(c)),(canon(w[::-1]),tuple(c[::-1]))) for w,c in raw})
tables=collections.defaultdict(set)
for w,c in keys:
    tables[canon(w)].add(encode(c));tables[canon(w[::-1])].add(encode(c[::-1]))
plan=read(HERE/'data/chunk-plan.json');literal=[];chunkpaths=[]
for i,name in enumerate(plan['chunks']):
    path=HERE/'lean'/(name+'.lean');chunkpaths.append(path);text=path.read_text()
    block=re.search(rf'def keys{i:02d} : List Key := (\[[\s\S]*?^\])',text,re.M).group(1)
    literal += [(tuple(a),tuple(b)) for a,b in ast.literal_eval(block)]
assert literal==keys and len(literal)==1378
oriented={(canon(w),tuple(c)) for w,c in literal}|{(canon(w[::-1]),tuple(c[::-1])) for w,c in literal}
assert len(oriented)==2678
lookup={}
for w,c in oriented:
    if w not in lookup:lookup[w]=np.zeros(6**len(c),dtype=bool)
    lookup[w][encode(c)]=True
directions=ROOT/'milestones/59-extended-share-window/extended/data/model.json';ext=read(directions)['extensions'];assert len(ext)==505
code=np.arange(6**6,dtype=np.int64);C=np.stack([code//6**j%6+1 for j in range(5,-1,-1)],axis=1)
folded={}
for width in range(2,7):
    for offset in range(7-width):
        vals=np.zeros(len(code),dtype=np.int64)
        for j in range(width):vals=6*vals+C[:,offset+j]-1
        folded[width,offset]=vals
masks=[];placements=0
for ds in ext:
    env=dict(ds=ds,code=code,keep=np.ones(len(code),dtype=bool),tables=tables,canon=canon,np=np)
    exec(loop,env);actual=env['keep'];expected=np.ones(len(code),dtype=bool)
    for width in range(2,7):
        for offset in range(7-width):
            word=canon(ds[offset+2:offset+width+3])
            if word in lookup:
                expected &= ~lookup[word][folded[width,offset]];placements+=1
    assert np.array_equal(actual,expected),ds
    masks.append(actual)
mask=np.stack(masks);rawmask=mask.tobytes();dest=HERE/'data/reference-filter-mask.u8.gz'
dest.write_bytes(gzip.compress(rawmask,compresslevel=6,mtime=0))
inputs=[Path(__file__).resolve(),builder,key235,key236,directions,HERE/'data/reference-union.json',HERE/'data/chunk-plan.json',
    HERE/'lean/ReferenceInterface.lean',HERE/'lean/ReferenceUnion.lean',*chunkpaths]
out=dict(status='PASS_EXACT_REFERENCE_FILTER_COMPARISON',canonical_keys=len(keys),oriented_pairs=len(oriented),
    direction_shapes=505,count_codes=46656,candidate_pairs=int(mask.size),applicable_placements=placements,
    accepted=int(mask.sum()),rejected=int((~mask).sum()),mask_sha256=hashlib.sha256(rawmask).hexdigest(),
    compressed_mask_sha256=sha(dest),inputs={p.relative_to(ROOT).as_posix():sha(p) for p in inputs},seconds=time.monotonic()-start,
    scope='Exact isolated reference-filter loop over every direction/count pair. Other filters and history duplication are excluded; these are not newly removed full-graph edges. Lean covers the literal keys and conditional guard theorem; Python execution is a separate check.')
(HERE/'data/filter-comparison.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],out['candidate_pairs'],'pairs;',out['accepted'],'accepted;',out['rejected'],'rejected;',round(out['seconds'],3),'seconds')
