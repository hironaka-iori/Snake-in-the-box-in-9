"""Enumerate complete compatible words for every emitted history share rule."""
from pathlib import Path
import collections,hashlib,itertools,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
model=ROOT/'milestones/67-critical-family-charge/data/full-model.json'
current=ROOT/'milestones/70-proof-supported-share-model/data/enriched-model.json'
directions=ROOT/'milestones/59-extended-share-window/extended/data/model.json'
old=read(model);new=read(current);assert old['patterns']==new['patterns']
extensions=read(directions)['extensions'];assert len(extensions)==505
ids={tuple(w):i for i,w in enumerate(extensions)}
def canon(word):
    seen=[];out=[]
    for x in word:
        if x not in seen:seen.append(x)
        out.append(seen.index(x))
    return out
def induced(word):
    vertices=[0]
    for x in word:
        v=vertices[-1]^(1<<x)
        if v in vertices or any((v^u).bit_count()==1 for u in vertices[:-1]):return False
        vertices.append(v)
    return True
def all_words(word=()):
    if len(word)==11:yield list(word);return
    for x in range(min(9,max(word,default=-1)+2)):
        nxt=word+(x,)
        if induced(nxt):yield from all_words(nxt)
words=list(all_words());assert len(words)==11162
by_sig=collections.defaultdict(list)
for w in words:by_sig[tuple(ids[tuple(canon(w[j:j+9]))] for j in range(3))].append(w)
rows=[]
for i,p in enumerate(new['patterns']):
    if p['mode']!='share':continue
    sig=p['signature'];prefix=extensions[sig[0]]
    variants=by_sig[tuple(sig)]
    restricted=[prefix+[a,b] for a,b in itertools.product(range(9),repeat=2)
      if canon(prefix+[a,b])==prefix+[a,b] and induced(prefix+[a,b])
      and [ids[tuple(canon((prefix+[a,b])[j:j+9]))] for j in range(3)]==sig]
    assert variants==restricted and variants
    if 'variants' in p:assert p['variants']==variants,(i,p['variants'],variants)
    if 'directions' in p:assert p['directions'] in variants
    rows.append(dict(share_index=len(rows),model_index=i,edge=p['edge'],signature=sig,variants=variants,
                     caps=p['caps'],geometric_lower=p['geometric_lower'],lower=p['lower'],
                     original_has_variants='variants' in p,original_directions=p.get('directions')))
assert len(rows)==len({tuple(r['signature']) for r in rows})==55
out=dict(status='PASS_COMPLETE_HISTORY_SHARE_VARIANTS_PYTHON',canonical_induced_eleven_shapes=len(words),
         share_rules=len(rows),variant_occurrences=sum(len(r['variants']) for r in rows),
         distinct_variant_words=len({tuple(w) for r in rows for w in r['variants']}),
         old_representative_rule_variant_counts=[dict(model_index=r['model_index'],variants=len(r['variants'])) for r in rows if not r['original_has_variants']],
         ambiguous_rules=[r['model_index'] for r in rows if len(r['variants'])>1],rows=rows,
         inputs={p.relative_to(ROOT).as_posix():sha(p) for p in [model,current,directions]},script_sha256=sha(Path(__file__)),
         scope='Complete eleven-word enumeration agrees with independent 81-tail enumeration for all55 share signatures. Lean finite covers and actual-snake credit transfer are separate.')
(HERE/'data/variants.json').write_text(json.dumps(out,indent=2)+'\n')
fmt=lambda x:'['+','.join(fmt(y) if isinstance(y,list) else str(y) for y in x)+']'
sources=[]
for chunk in range(11):
    lines=['import HistoryShareCover','','namespace Snake9.HistoryShare94',
           'set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option Elab.async false','']
    for r in rows[chunk*5:(chunk+1)*5]:
        tag=f"{r['share_index']:03}"
        lines += [f'def signature{tag} : List Nat := {fmt(r["signature"])}',
                  f'def variants{tag} : List (List Nat) := {fmt(r["variants"])}',
                  f'theorem share_cover_{tag} : shareCoverTable signature{tag} variants{tag} = true := by',
                  '  decide +kernel',f'#print axioms share_cover_{tag}','']
    lines+=['end Snake9.HistoryShare94','']
    name=f'ShareCover{chunk:02}';p=HERE/'lean'/(name+'.lean');p.write_text('\n'.join(lines))
    sources.append(dict(module=name,source_sha256=sha(p),share_indices=list(range(chunk*5,(chunk+1)*5))))
(HERE/'data/cover-generation.json').write_text(json.dumps(dict(status='GENERATED_PENDING_LEAN',sources=sources,
    variants_sha256=sha(HERE/'data/variants.json'),script_sha256=sha(Path(__file__))),indent=2)+'\n')
print(out['status'],len(rows),'rules',out['variant_occurrences'],'variant occurrences;',len(out['ambiguous_rules']),'ambiguous signatures')
print('Old representative-only counts:',out['old_representative_rule_variant_counts'])
