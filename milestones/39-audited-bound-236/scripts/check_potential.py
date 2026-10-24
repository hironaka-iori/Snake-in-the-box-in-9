"""Independent enumeration of the finite inequality printed in the revision."""
from pathlib import Path
import ast, hashlib, itertools, json, re
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
source=HERE/'upstream/work/spectral/stronger/WindowAutomaton5R4Data.lean'
text=source.read_text(encoding='utf-8')
shapes=ast.literal_eval(re.search(r'def shapes7R4 : List \(List Nat\) := (\[.*\])',text).group(1))
part=text.split('def potMaskOf5R4')[1].split('def cntIdx5R4')[0]
masks={int(i):int(n) for i,n in re.findall(r'if s = (\d+) then (\d+) else',part)}
assert len(masks)==34
pots={tuple(ds):[(masks[i]>>(6*j))&63 for j in range(6**4)] for i,ds in enumerate(shapes)}
def canon(ds):
 names={};return tuple(names.setdefault(d,len(names)) for d in ds)
def induced(ds):
 vertices=[0]
 for d in ds:vertices.append(vertices[-1]^(1<<d))
 return len(set(vertices))==len(vertices) and all((vertices[i]^vertices[j]).bit_count()!=1 for i in range(len(vertices)) for j in range(i+2,len(vertices)))
def rgs(n,p=()):
 if not n:yield p;return
 for d in range(max(p,default=-1)+2):yield from rgs(n-1,p+(d,))
words7=[w for w in rgs(7) if induced(w)]
words8=[w for w in rgs(8) if induced(w)]
assert set(words7)==set(pots) and len(words7)==34
keys=json.loads((HERE/'data/exclusion-catalogue.json').read_text())
forbidden={}
for ds,cs in keys:
 forbidden.setdefault(tuple(ds),set()).add(tuple(cs))
 forbidden.setdefault(canon(ds[::-1]),set()).add(tuple(cs[::-1]))
tested=allowed=0
for ds in words8:
 f=[forbidden.get(canon(ds[-(k+1):]),set()) for k in range(2,6)]
 before=pots[canon(ds[:7])];after=pots[canon(ds[1:])]
 for t1,t2,t3,t4,b in itertools.product(range(1,7),repeat=5):
  tested+=1
  counts=(t1,t2,t3,t4,b)
  if any(counts[-k:] in f[k-2] for k in range(2,6)):continue
  i=(((t1-1)*6+t2-1)*6+t3-1)*6+t4-1
  j=(((t2-1)*6+t3-1)*6+t4-1)*6+b-1
  assert 42+after[j]<=11*b+before[i],(ds,counts,before[i],after[j])
  allowed+=1
out=dict(status='PASSED',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),direction_shapes_7=len(words7),induced_words_8=len(words8),states=len(pots)*6**4,potential_min=min(map(min,pots.values())),potential_max=max(map(max,pots.values())),candidate_transitions=tested,permitted_transitions=allowed,exclusion_rows=len(keys),scope='Independent arithmetic verification of the table inequality; does not replay local geometric refutations.')
(HERE/'data/potential-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
