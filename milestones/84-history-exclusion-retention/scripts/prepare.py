"""Pin the three history exclusions and enumerate every compatible shape."""
from pathlib import Path
import hashlib,itertools,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
model=ROOT/'milestones/67-critical-family-charge/data/full-model.json'
current=ROOT/'milestones/70-proof-supported-share-model/data/enriched-model.json'
directions=ROOT/'milestones/59-extended-share-window/extended/data/model.json'
old=read(model);new=read(current);assert old['patterns']==new['patterns']
rows=[r for r in new['patterns'] if r['mode']=='exclusion'];assert len(rows)==3
extensions=read(directions)['extensions'];assert len(extensions)==505
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
ids={tuple(w):i for i,w in enumerate(extensions)}
for row in rows:
    sig=row['signature'];prefix=extensions[sig[0]]
    variants=[w for w in words if [ids[tuple(canon(w[j:j+9]))] for j in range(3)]==sig]
    restricted=[prefix+[a,b] for a,b in itertools.product(range(9),repeat=2)
      if canon(prefix+[a,b])==prefix+[a,b] and induced(prefix+[a,b])
      and [ids[tuple(canon((prefix+[a,b])[j:j+9]))] for j in range(3)]==sig]
    assert variants==restricted==[row['directions']],(sig,variants)
    row['compatible_variants']=variants
    row['count_digit']=int(next(iter(row['caps'])))
    assert len(row['caps'])==1 and next(iter(row['caps'].values()))==2
    row['long_window_position']=row['count_digit']+5
out=dict(status='PASS_THREE_UNIQUE_HISTORY_REALIZATIONS_PYTHON',canonical_induced_eleven_shapes=len(words),
    rows=rows,inputs={p.relative_to(ROOT).as_posix():sha(p) for p in [model,current,directions]},
    scope='Independent complete eleven-shape enumeration and separate 81-pair prefix enumeration. Lean uniqueness and actual-snake transport are separate gates.')
(HERE/'data/realizations.json').write_text(json.dumps(out,indent=2)+'\n')
fmt=lambda xs:'['+','.join(map(str,xs))+']'
lines=['import IntervalGuards','', 'namespace Snake9.History84',
 'open Snake9.WindowAutomaton Snake9.Direction77', 'set_option maxRecDepth 100000',
 'set_option maxHeartbeats 2000000','',
 'def realizes (sig cs : List Nat) : Bool :=',
 '  (canon (cs.take 9) == extensions.getD (sig.getD 0 0) []) &&',
 '  (canon ((cs.drop 1).take 9) == extensions.getD (sig.getD 1 0) []) &&',
 '  (canon ((cs.drop 2).take 9) == extensions.getD (sig.getD 2 0) [])','',
 'def realizationTable (sig expected : List Nat) : Bool :=',
 '  allBelow 9 fun a => allBelow 9 fun b =>',
 '    let cs := extensions.getD (sig.getD 0 0) [] ++ [a,b]',
 '    !isRGS cs 0 || !inducedPattern cs || !realizes sig cs || (cs == expected)','']
for i,row in enumerate(rows):
    lines += [f'def signature{i} : List Nat := {fmt(row["signature"])}',
      f'def word{i} : List Nat := {fmt(row["directions"])}',
      f'theorem realization_table_{i} : realizationTable signature{i} word{i} = true := by',
      '  decide +kernel',f'#print axioms realization_table_{i}','']
lines += ['end Snake9.History84','']
(HERE/'lean/HistoryRealizations.lean').write_text('\n'.join(lines))
print(out['status'],len(words),'shapes;',len(rows),'singleton classes')
