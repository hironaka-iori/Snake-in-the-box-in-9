"""Verify the pinned evidence and manuscript; not a replay of the full upstream proof."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[3]; HERE=Path(__file__).resolve().parents[1]
manifest=json.loads((HERE/'data/upstream-manifest.json').read_text())
for entry in manifest['files']:
 data=(HERE/'upstream'/entry['path']).read_bytes()
 assert hashlib.sha256(data).hexdigest()==entry['sha256']
 assert data==subprocess.check_output(['git','show',manifest['commit']+':'+entry['path']],cwd=ROOT)
audit=(HERE/'upstream/outputs/upper-bound-236-audit-linux.log').read_text()
for name in ['upper_bound_236','verified_interval_191_236']:
 assert "'Snake9."+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in audit
assert '# AXIOM AUDIT PASSED' in audit and '# chain wall time 3716s; exit 0' in audit
assert 'sorryAx' not in audit
assembly=(HERE/'upstream/work/final_lean/LocalWindowDirUnsatR4.lean').read_text()
roots=re.findall(r'(?:refine ⟨|exact )([QR]\w+)\.unsat',assembly)
assert len(roots)==len(set(roots))==732
assert sum(r.startswith('Q') for r in roots)==371
assert sum(r.startswith('R') for r in roots)==361
assert 'allRefuted236_of_unsat allUnsat236' in assembly
theorem=(HERE/'upstream/work/spectral/stronger/UpperBound236.lean').read_text()
assert 'upper_236_of_refuted LocalWindow.allRefuted236 p' in theorem
potential=json.loads((HERE/'data/potential-verification.json').read_text())
assert potential['status']=='PASSED' and potential['exclusion_rows']==732
assert potential['source_sha256']==hashlib.sha256((HERE/'upstream/work/spectral/stronger/WindowAutomaton5R4Data.lean').read_bytes()).hexdigest()
log=(HERE/'logs/Bound236Arithmetic.log').read_text()
assert log.count('depends on axioms:')==4 and 'sorryAx' not in log and 'error:' not in log
base='a87f26ee03b1f7ceeb4cb65a7fcf7f4e7f549fa9'
old=subprocess.check_output(['git','show',base+':paper/snake9_research.tex'],cwd=ROOT).decode('utf-8').replace('\r\n','\n')
p=ROOT/'paper/snake9_research.tex';new=p.read_text(encoding='utf-8')
assert Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()==p.read_bytes()
assert old.split('\\begin{abstract}')[0]==new.split('\\begin{abstract}')[0]
labels=re.findall(r'\\label\{([^}]+)\}',new)
assert len(labels)==len(set(labels))
assert set(re.findall(r'\\label\{([^}]+)\}',old))<=set(labels)
assert set(re.findall(r'\\(?:ref|eqref)\{([^}]+)\}',new))<=set(labels)
cites={x for xs in re.findall(r'\\cite\{([^}]+)\}',new) for x in xs.split(',')}
assert cites<=set(re.findall(r'\\bibitem\{([^}]+)\}',new))
stack=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',new):
 if m[1]=='begin':stack.append(m[2])
 else:assert stack and stack.pop()==m[2]
assert not stack
clean=re.sub(r'\\url\{[^}]*\}',r'URL',new)
clean=re.sub(r'(?<!\\)%[^\n]*','',clean);clean=re.sub(r'\\[{}$%]','',clean)
level=0
for c in clean:
 if c=='{':level+=1
 if c=='}':level-=1
 assert level>=0
assert level==0 and clean.count('$')%2==0
for a,b in [(r'\[',r'\]'),(r'\(',r'\)')]:assert clean.count(a)==clean.count(b)
rx=r'\\begin\{(theorem|lemma|proposition|corollary|conjecture)\}(.*?)\\end\{\1\}'
norm=lambda t:re.sub(r'\s+',' ',t).strip()
statements=lambda t:Counter((k,norm(s)) for k,s in re.findall(rx,t,re.S))
removed=list((statements(old)-statements(new)).elements())
assert len(removed)==1 and r'\label{thm:main}' in removed[0][1]
assert sum(statements(new).values())==sum(statements(old).values())+3
a=r'\section{Explicit transition sequences and blockers}';b=r'\begin{thebibliography}'
assert old[old.index(a):old.index(b)].strip()==new[new.index(a):new.index(b)].strip()
out=dict(status='PASSED',upstream_commit=manifest['commit'],snapshot_files_verified=len(manifest['files']),certificate_roots=732,reused_roots=371,new_roots=361,local_full_rebuild=False,local_arithmetic_audits=4,potential_verification=potential,paper_baseline=base,paper_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),editor_identical=True,preamble_preserved=True,statements=len(list(re.finditer(rx,new,re.S))),only_changed_prior_statement='thm:main: upper endpoint 238 to 236',added_statements=3,witness_appendix_unchanged=True,labels=len(labels),latex_compilation='Blocked before TeX: Windows restricted-token runner cannot prepare split writable roots. No rendered-page verification.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
