import json,collections,re,sys
from pathlib import Path
def norm(s):
 r={};return ''.join(str(r.setdefault(z,len(r))) for z in s)
def canonical(s):return min(norm(s),norm(s[::-1]))
sources=collections.defaultdict(set); targets={canonical(l.split()[0]) for l in open(sys.argv[1])}
def check_word(w,f):
 for n in (96,97,98):
  for i in range(len(w)-n+1):
   k=canonical(w[i:i+n])
   if k in targets:sources[k].add(f)
def walk(p,f):
 if isinstance(p,dict):
  for v in p.values():walk(v,f)
 if not isinstance(p,list):return
 if p and all(type(a) is int for a in p) and len(p) in (97,98,99) and min(p)>=0 and max(p)<256:
  s=set(p)
  if len(p)!=len(s):return
  adj={x:[x^1<<i for i in range(8) if x^1<<i in s] for x in s};ends=[x for x,A in adj.items() if len(A)==1]
  if len(ends)!=2 or max(map(len,adj.values()))>2:return
  path=ends[:1]
  while True:
   opts=[x for x in adj[path[-1]] if len(path)==1 or x!=path[-2]]
   if not opts:break
   path.append(opts[0])
  if len(path)==len(p):check_word(''.join(str((u^v).bit_length()-1) for u,v in zip(path,path[1:])),f)
 else:
  for x in p:
   if isinstance(x,(list,dict)):walk(x,f)
for f in Path('.').glob('q8*'):
 if not f.is_file() or f.suffix not in ('.txt','.json','.jsonl','.log'):continue
 t=f.read_text()
 for w in set(re.findall(r'(?<![0-9a-zA-Z])[0-7]{96,98}(?![0-9a-zA-Z])',t)):check_word(w,f.name)
 if f.suffix=='.json':walk(json.loads(t),f.name)
 if f.suffix=='.jsonl':
  for l in t.splitlines():walk(json.loads(l),f.name)
print('by length',collections.Counter(map(len,sources)),'matching files',collections.Counter(n for v in sources.values() for n in v))
for w,files in sorted(sources.items()):print(w,','.join(sorted(files)))
