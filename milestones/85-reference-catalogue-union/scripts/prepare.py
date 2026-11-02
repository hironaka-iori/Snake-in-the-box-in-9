"""Preserve exact catalogue sources and identify the reference union."""
from pathlib import Path
import ast,collections,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();read=lambda p:json.loads(p.read_text())
pins={'235':'74ca83db9c218446211d4f24c5e5a07329fdd847','236':'7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b'}
specs=[('235','LocalWindowDirKeys6K235','work/final_lean/LocalWindowDirKeys6K235.lean'),
       ('235','LocalWindowDirGlue6K235','work/final_lean/LocalWindowDirGlue6K235.lean'),
       ('236','LocalWindowDirKeysR4','work/final_lean/LocalWindowDirKeysR4.lean')]
upstream={}
for pin,name,path in specs:
    raw=subprocess.check_output(['git','-c','core.commitGraph=false','show',pins[pin]+':'+path],cwd=ROOT)
    dest=HERE/'upstream'/(name+'.lean')
    if dest.exists():assert dest.read_bytes()==raw
    else:dest.write_bytes(raw)
    upstream[name]=dict(commit=pins[pin],git_path=path,sha256=sha(dest))
    if name in ['LocalWindowDirKeys6K235','LocalWindowDirKeysR4']:
        (HERE/'lean'/(name+'.lean')).write_bytes(raw)
def parse(name):
    text=(HERE/'upstream'/(name+'.lean')).read_text()
    return [(tuple(ast.literal_eval(a)),tuple(ast.literal_eval(b))) for a,b in
      re.findall(r'\(\s*(\[[\d, ]*\])\s*,\s*(\[[\d, ]*\])\s*\)',text)]
key235=ROOT/'milestones/54-share-coverage/data/keys_235.json'
key236=ROOT/'milestones/39-audited-bound-236/data/exclusion-catalogue.json'
a=[(tuple(w),tuple(lo for lo,hi in bounds)) for w,bounds in read(key235)['keys']]
for w,bounds in read(key235)['keys']:
    assert all((lo==hi and 1<=lo<6) or (lo,hi)==(6,21) for lo,hi in bounds)
b=[(tuple(w),tuple(c)) for w,c in read(key236)]
assert a==parse('LocalWindowDirKeys6K235') and len(a)==1287
assert b==parse('LocalWindowDirKeysR4') and len(b)==732
def canon(w):
    seen=list(dict.fromkeys(w));return tuple(seen.index(x) for x in w)
def rev(key):return (canon(key[0][::-1]),key[1][::-1])
norm=lambda k:min((canon(k[0]),k[1]),rev(k))
A={norm(k) for k in a};B={norm(k) for k in b};union=sorted(A|B)
assert (len(A),len(B),len(A&B),len(union))==(1287,732,641,1378)
direct=set(a)|set(b);missing=[k for k in union if k not in direct]
assert not missing,('Canonical representative needs reversal transport',len(missing))
oriented=sorted(set(union)|{rev(k) for k in union});assert len(oriented)==2678
rows=[]
for k in union:
    which,index=(235,a.index(k)) if k in a else (236,b.index(k))
    rows.append(dict(directions=k[0],symbols=k[1],source_catalogue=which,source_index=index))
out=dict(status='PASS_REFERENCE_UNION_SOURCE_COMPARISON',catalogue_sizes=[1287,732],intersection=641,union=1378,
    oriented_pairs=2678,width_histogram=dict(sorted(collections.Counter(len(c) for w,c in union).items())),
    rows=rows,all_union_representatives_present_directly=True,upstream=upstream,
    inputs={p.relative_to(ROOT).as_posix():sha(p) for p in [key235,key236]},
    scope='Exact source/JSON comparison and provenance for every union representative. Closed refutation imports and Lean membership checks are separate obligations.')
(HERE/'data/reference-union.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],'1378 direct representatives; 2678 oriented pairs')
