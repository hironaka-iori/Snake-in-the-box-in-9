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
prior=R/'milestones/141-zero-credit-comparison/data/paper-source-review.json'
prior_review=json.loads(prior.read_text())
assert prior_review['source_sha256']==sha(old)
def appendix(x):
 return x.split('\\section{Odd-length witnesses attaining pair sum nine}',1)[1].split('\\begin{thebibliography}',1)[0]
assert appendix(s)==appendix(previous)
witness_reviews=prior_review['printed_witnesses_reused']
out=dict(status='PASS_SOURCE_STRUCTURE_AND_UNCHANGED_WITNESS_APPENDIX',source_sha256=sha(source),
 preamble_and_authors_unchanged=True,definition_environment_count=s.count('\\begin{definition}'),
 labels=len(labels),references=len(refs),bibliography_entries=len(bibs),citation_occurrences=len(cites),
 balanced_braces_and_environments=True,printed_witnesses_reused=witness_reviews,prior_witness_check_sha256=sha(prior.read_bytes()),
 pdf_rebuilt=False,visual_layout_checked=False,
 scope='Static TeX structure and reference resolution. The unchanged witness appendix reuses the pinned round136 reconstruction. The built-in compiler failed before TeX execution.')
(H/'data/paper-source-review.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
