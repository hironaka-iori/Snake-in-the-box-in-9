"""Check the full revision against its frozen source and preservation rules."""
from pathlib import Path
import hashlib,importlib.util,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('paper156_revision',H/'scripts/revise_paper.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
revision=read(H/'data/paper-revision.json')
raw=(R/'paper/snake9_research.tex').read_bytes()
assert raw==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
old=(H/'audit/paper-before156.tex.txt').read_bytes()
assert sha(old)==revision['source_sha256_before'] and sha(raw)==revision['source_sha256_after']
text=raw.decode('utf-8');expected,operations=module.transform(old.decode('utf-8'))
assert text==expected and operations==revision['operations']
assert module.invariants(old.decode('utf-8'),text)==revision['preserved']
for p,d in revision['source_files_sha256'].items():assert sha((R/p).read_bytes())==d,p
clean=re.sub(r'\\url\{[^}]*\}',lambda m:m[0].replace('%','x'),text)
clean=re.sub(r'(?<!\\)%[^\n]*','',clean);stack=[]
for match in re.finditer(r'\\(begin|end)\{([^}]+)\}',clean):
    action,name=match.groups()
    if action=='begin':stack.append(name)
    else:assert stack and stack.pop()==name,(name,match.start())
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
assert json.loads(comp['result']['content'][0]['text'])['kind']=='success'
out=dict(status='PASS_FULL_PAPER_REVISION156_AND_COMPILATION',paper_sha256=sha(raw),
    full_source_review=True,exact_documented_revision=True,authors_preamble_hypersetup_unchanged=True,
    original_proof_and_witness_bytes_preserved=revision['preserved'],new_definitions=0,
    labels=len(labels),references=len(refs),bibliography_entries=len(bibs),citation_occurrences=len(cites),
    pdf_rebuilt=True,visual_layout_checked=False,last_full_revision=156,next_full_revision=166)
(H/'data/paper-source-review.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(out))
