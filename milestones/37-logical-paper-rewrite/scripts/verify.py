"""Source integrity checks, distinct from a LaTeX compilation or a proof rebuild."""
from pathlib import Path
from collections import Counter
import hashlib, json, re, subprocess
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
BASE='ffdf1b94403396a1b8ddaffdae419bb897ba5cf8'
old=subprocess.check_output(['git','-c','safe.directory=E:/Snake-in-a-box','show',BASE+':paper/snake9_research.tex'],cwd=ROOT).decode('utf-8').replace('\r\n','\n')
paper=ROOT/'paper/snake9_research.tex'
new=paper.read_text(encoding='utf-8')
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert paper.read_bytes()==editor.read_bytes()
assert old.split('\\begin{abstract}')[0]==new.split('\\begin{abstract}')[0]
labels=re.findall(r'\\label\{([^}]+)\}',new)
assert len(labels)==len(set(labels)),[x for x,c in Counter(labels).items() if c>1]
assert set(re.findall(r'\\label\{([^}]+)\}',old))<=set(labels)
refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',new)
assert set(refs)<=set(labels)
cites={k for group in re.findall(r'\\cite\{([^}]+)\}',new) for k in group.split(',')}
assert cites<=set(re.findall(r'\\bibitem\{([^}]+)\}',new))
stack=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',new):
 if m[1]=='begin':stack.append(m[2])
 else:assert stack and stack.pop()==m[2],(m.start(),m[2])
assert not stack
# Escaped braces, comments and escaped dollars are excluded from this lexical check.
clean=re.sub(r'\\url\{[^}]*\}',lambda m:r'\url{URL}',new)
clean=re.sub(r'(?<!\\)%[^\n]*','',clean)
clean=re.sub(r'\\[{}$%]','',clean)
level=0
for c in clean:
 if c=='{':level+=1
 if c=='}':level-=1
 assert level>=0
assert level==0 and clean.count('$')%2==0
for opening,closing in [(r'\[',r'\]'),(r'\(',r'\)')]:
 assert clean.count(opening)==clean.count(closing)
# The complete printed witness appendix is preserved, including all transition words.
start=r'\section{Explicit transition sequences and blockers}'
finish=r'\begin{thebibliography}'
assert old[old.index(start):old.index(finish)].strip()==new[new.index(start):new.index(finish)].strip()
statement_re=r'\\begin\{(theorem|lemma|proposition|corollary|conjecture)\}(.*?)\\end\{\1\}'
norm=lambda t:re.sub(r'\s+',' ',t).strip()
old_statements=Counter((k,norm(s)) for k,s in re.findall(statement_re,old,re.S))
new_statements=Counter((k,norm(s)) for k,s in re.findall(statement_re,new,re.S))
changed=list((old_statements-new_statements).elements())
allowed={'thm:main','prop:direction238','thm:upper238','prop:direction239'}
for kind,s in changed:
 ls=set(re.findall(r'\\label\{([^}]+)\}',s))
 assert ls & allowed,(kind,s)
# Compare the printed catalogue with both the JSON and original proof input.
keys=json.loads((HERE/'data/exclusion-catalogue.json').read_text())
rows=re.findall(r'^\d+ & \$\(([^)]+)\)\$ & \$\(([^)]+)\)\$\\\\$',new,re.M)
printed=[[[int(x) for x in a.split(',')],[int(x) for x in b.split(',')]] for a,b in rows]
assert printed==keys and len(keys)==175
proof_source=(ROOT/'work/final_lean/LocalWindowDirKeys5.lean').read_text(encoding='utf-8')
proof_part=proof_source.split('def dirKeys5 :')[1].split(']\n')[0]
proof_keys=[[[int(x) for x in re.findall(r'\d+',a)],[int(x) for x in re.findall(r'\d+',b)]] for a,b in re.findall(r'\(\[([^]]+)\], \[([^]]+)\]\)',proof_part)]
assert keys==proof_keys
potential=json.loads((HERE/'data/potential-verification.json').read_text())
assert potential['status']=='PASSED'
potential_source=ROOT/'work/spectral/stronger/WindowAutomaton5Data.lean'
assert potential['source_sha256']==hashlib.sha256(potential_source.read_bytes()).hexdigest()
log=(HERE/'logs/PaperArithmetic.log').read_text(encoding='utf-8')
assert 'sorryAx' not in log and 'error:' not in log and log.count('depends on axioms:')==5
assert all(set(re.search(r'\[([^]]*)\]',line)[1].split(', '))<={'propext','Classical.choice','Quot.sound'} for line in log.splitlines() if 'depends on axioms:' in line)
build=Path((HERE/'build/latest.txt').read_text().strip())
assert (build/'PaperArithmetic.olean').exists()
assert (HERE/'lean/PaperArithmetic.lean').stat().st_mtime<=(build/'PaperArithmetic.olean').stat().st_mtime
out=dict(status='PASSED',baseline_commit=BASE,paper_sha256=hashlib.sha256(paper.read_bytes()).hexdigest(),editor_identical=True,preamble_authors_hypersetup_preserved=True,original_labels_preserved=72,total_labels=len(labels),original_statements=sum(old_statements.values()),revised_statements=sum(new_statements.values()),restated_statement_labels=[re.findall(r'\\label\{([^}]+)\}',s)[0] for _,s in changed],witness_appendix_unchanged=True,exclusion_rows=len(keys),potential_transitions_checked=potential['candidate_transitions'],lean_arithmetic_audits=5,latex_compilation='Blocked before TeX by Windows restricted-token split-root configuration',scope='Source structure and supplementary arithmetic; no rendered-page verification and no new independent rebuild of the 238 proof.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
