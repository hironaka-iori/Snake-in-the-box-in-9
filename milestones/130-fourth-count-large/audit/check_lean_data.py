"""Independently parse concrete Lean certificate data and compare with the new CNF tail."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=H/'lean/LargeClauses130.lean';s=source.read_text(encoding='utf-8')
d=json.loads((H/'data/large-counter.json').read_text())
block=s.split('def raw : List (List Nat) := ',1)[1].lstrip()
encoded,_=json.JSONDecoder().raw_decode(block)
decode=lambda x: -(x//2) if x%2 else x//2
assert [[decode(x) for x in c] for c in encoded]==d['clauses']
tagblock=s.split('def tags : List Tag := [',1)[1].split(']',1)[0].strip()
tags=[]
for name,args in re.findall(r'\(\.(\w+) ([\d ]+)\)',tagblock):tags.append([name]+list(map(int,args.split())))
assert tags==d['tags'] and len(tags)==717
assert re.sub(r'\(\.\w+ [\d ]+\)|[\s,\]]','',tagblock)==''
counter=re.search(r'def counter : Ctr := ⟨(\[[\d,]+\]),(\d+),\.ends⟩',s)
assert counter and json.loads(counter.group(1))==[2*x for x in d['literals']] and int(counter.group(2))==17
assert 'def counters : List Ctr := List.replicate 9 dfltCtr ++ [counter]' in s
treeblock=re.split(r'\n(?:noncomputable )?def counter : Ctr :=',s.split('def meaning : MT :=',1)[1],maxsplit=1)[0].strip()
tokens=re.findall(r'\(|\)|\.[a-zA-Z]+|\d+',treeblock)
assert ''.join(tokens)==re.sub(r'\s+','',treeblock)
pos=0
def parse():
 global pos
 if tokens[pos]=='.z':pos+=1;return ('z',)
 assert tokens[pos]=='(';pos+=1
 name=tokens[pos];pos+=1
 if name=='.n':node=('n',parse(),parse())
 elif name in ['.p','.e','.r']:
  n=3 if name=='.r' else 1
  args=list(map(int,tokens[pos:pos+n]));pos+=n;node=(name[1:],*args)
 else:raise AssertionError(name)
 assert tokens[pos]==')';pos+=1
 return node
tree=parse();assert pos==len(tokens)
def lookup(v):
 t=tree
 while t[0]=='n':t=t[1+v%2];v//=2
 return t
expected={v+1:('p',v) for v in range(512)}|{int(k):tuple(v) for k,v in d['registers'].items()}
for v in range(9063):assert lookup(v)==expected.get(v,('z',)),v
lines=(H/'work/large.cnf').read_text().splitlines()
tail=[[int(x) for x in line.split()[:-1]] for line in lines[-717:]]
assert tail==d['clauses']
assert all(abs(x)<=512 or 8706<=abs(x)<=9062 for c in tail for x in c)
out=dict(status='PASS_EXACT_LEAN_LARGE_DATA_AND_CNF_TAIL',clauses=717,tags=717,
 meanings_checked=9063,registers=357,occurrences=21,distinct_vertices=21,
 pins={p.relative_to(H).as_posix():sha(p) for p in [source,H/'data/large-counter.json',H/'work/large.cnf',Path(__file__)]},
 scope='Independent parsing of concrete Lean raw clauses, tags, counter literals and all variable meanings through9062. This is a data match, separate from the Lean theorem and from any full-CNF contradiction.')
path=H/'data/lean-data-review.json';assert not path.exists()
path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
