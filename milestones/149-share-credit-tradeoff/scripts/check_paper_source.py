"""Verify the targeted addition and distinguish source checks from PDF compilation."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
raw=(R/'paper/snake9_research.tex').read_bytes()
assert raw==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
old=(H/'audit/paper-before149.tex.txt').read_bytes();rev=read(H/'data/paper-revision.json')
assert sha(old)==rev['source_sha256_before'] and sha(raw)==rev['source_sha256_after']
text=raw.decode('utf-8');before=old.decode('utf-8')
assert before.replace(rev['insertion_anchor'],rev['added_text']+rev['insertion_anchor']).replace(
    '\\end{thebibliography}',rev['added_bibliography_entry']+'\\end{thebibliography}')==text
assert text.split('\\begin{document}',1)[0]==before.split('\\begin{document}',1)[0]
assert '.lean' not in text and text.count('\\begin{definition}')==before.count('\\begin{definition}')
clean=re.sub(r'\\url\{[^}]*\}',lambda m:m[0].replace('%','x'),text)
clean=re.sub(r'(?<!\\)%[^\n]*','',clean);stack=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',clean):
    action,name=m.groups()
    if action=='begin':stack.append(name)
    else:assert stack and stack.pop()==name,(name,m.start())
assert not stack
depth=0
for i,c in enumerate(clean):
    if c not in '{}':continue
    j=i-1
    while j>=0 and clean[j]=='\\':j-=1
    if (i-1-j)%2:continue
    depth+=1 if c=='{' else -1;assert depth>=0,i
assert depth==0
labels=re.findall(r'\\label\{([^}]+)\}',clean)
refs=re.findall(r'\\(?:ref|eqref|pageref|autoref)\{([^}]+)\}',clean)
bibs=re.findall(r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}',clean)
cites=[x.strip() for g in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',clean) for x in g.split(',')]
assert len(labels)==len(set(labels)) and not set(refs)-set(labels)
assert len(bibs)==len(set(bibs)) and not set(cites)-set(bibs)
comp=read(H/'data/paper-compile.json');assert comp['paper_sha256']==sha(raw)
payload=json.loads(comp['result']['content'][0]['text'])
assert payload['kind']=='compile-failed' and 'Compiler helper failed' in payload['diagnostics']['log']
out=dict(status='PASS_TARGETED_PAPER_SOURCE_CHECKS',source_sha256=sha(raw),
    preamble_and_authors_unchanged=True,exact_insertion_only=True,new_definitions=0,
    labels=len(labels),references=len(refs),bibliography_entries=len(bibs),citation_occurrences=len(cites),
    balanced_braces_and_environments=True,pdf_rebuilt=False,visual_layout_checked=False,
    last_full_revision=146,next_full_revision=156)
(H/'data/paper-source-review.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(out))
