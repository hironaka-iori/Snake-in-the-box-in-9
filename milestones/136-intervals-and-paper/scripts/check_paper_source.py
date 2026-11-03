"""Source checks only; they do not certify compilation or the PDF layout."""
from pathlib import Path
import collections,hashlib,itertools,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
repo=R/'paper/snake9_research.tex'
sha=lambda b:hashlib.sha256(b).hexdigest()
source=editor.read_bytes();assert source==repo.read_bytes()
old=(H/'audit/paper-before.tex.txt').read_bytes()
s=source.decode('utf-8');previous=old.decode('utf-8')
assert s.split('\\begin{document}',1)[0]==previous.split('\\begin{document}',1)[0]
assert '.lean' not in s
assert s.count('\\begin{definition}')==previous.count('\\begin{definition}')
# Percent escapes inside \url are handled by that command, not TeX comments.
masked=re.sub(r'\\url\{[^}]*\}',lambda m:m[0].replace('%','x'),s)
text=re.sub(r'(?<!\\)%[^\n]*','',masked)
stack=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',text):
 action,name=m.groups()
 if action=='begin':stack.append(name)
 else:assert stack and stack.pop()==name,(name,m.start())
assert not stack
depth=0
for i,c in enumerate(text):
 if c not in '{}':continue
 j=i-1
 while j>=0 and text[j]=='\\':j-=1
 if (i-1-j)%2:continue
 depth+=1 if c=='{' else -1
 assert depth>=0,i
assert depth==0
labels=re.findall(r'\\label\{([^}]+)\}',text)
assert len(labels)==len(set(labels)),[x for x,n in collections.Counter(labels).items() if n>1]
refs=re.findall(r'\\(?:ref|eqref|pageref|autoref)\{([^}]+)\}',text)
assert not(set(refs)-set(labels)),set(refs)-set(labels)
bibs=re.findall(r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}',text)
cites=[x.strip() for group in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',text) for x in group.split(',')]
assert len(bibs)==len(set(bibs)) and not(set(cites)-set(bibs))
record=json.loads((H/'data/paper-revision.json').read_text())
assert sha(source)==record['after_sha256'] and sha(old)==record['before_sha256']
witness_reviews=[]
newappendix=s.split('\\section{Odd-length witnesses attaining pair sum nine}',1)[1].split('\\begin{thebibliography}',1)[0]
quotes=re.findall(r'\\begin\{quote\}\\ttfamily\\small\n(.*?)\\end\{quote\}',newappendix,re.S)
assert len(quotes)==2
for row,quote,expected in zip(record['witnesses'],quotes,[[8,6,10,3,8],[11,4,13,5,12]]):
 digits=''.join(re.findall('[0-8]',quote));assert digits==row['directions']
 v=[row['initial']]
 for d in digits:v.append(v[-1]^(1<<int(d)))
 assert len(v)==row['edges']+1 and v[-1]==row['final'] and len(set(v))==len(v)
 assert all(((v[i]^v[j]).bit_count()==1)==(j==i+1) for i in range(len(v)) for j in range(i+1,len(v)))
 r=row['start'];assert v[r:r+7]==[0,1,3,7,6,14,10]
 selected=set(v);counts=[]
 for index in range(r+1,r+6):
  x=v[index]
  counts.append(sum(all(y not in selected for y in [x^(1<<a),x^(1<<b),x^(1<<a)^(1<<b)]) for a,b in itertools.combinations(range(9),2)))
 assert counts==expected and [counts[1],counts[3]]==row['pair']
 endpoint_distances=[[(e^v[i]).bit_count() for i in [r+2,r+4]] for e in [v[0],v[-1]]]
 assert endpoint_distances.count([2,2])==1
 witness_reviews.append(dict(edges=row['edges'],pairs_checked=len(v)*(len(v)-1)//2,counts=counts,endpoint_distances=endpoint_distances))
out=dict(status='PASS_SOURCE_STRUCTURE_AND_PRINTED_WITNESSES',source_sha256=sha(source),
 preamble_and_authors_unchanged=True,definition_environment_count=s.count('\\begin{definition}'),
 labels=len(labels),references=len(refs),bibliography_entries=len(bibs),citation_occurrences=len(cites),
 balanced_braces_and_environments=True,printed_witnesses=witness_reviews,
 pdf_rebuilt=False,visual_layout_checked=False,
 scope='Static TeX structure, reference resolution and exact printed witness reconstruction only. The built-in compiler failed before TeX execution.')
(H/'data/paper-source-review.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
