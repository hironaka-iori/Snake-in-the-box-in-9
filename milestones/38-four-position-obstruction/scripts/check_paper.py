"""Check the additive manuscript update without changing earlier audit receipts."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
BASE='1f2a40aae91283c43f9de759f9d2d572d30a10ac'
old=subprocess.check_output(['git','-c','safe.directory=E:/Snake-in-a-box','show',BASE+':paper/snake9_research.tex'],cwd=ROOT).decode('utf-8').replace('\r\n','\n')
p=ROOT/'paper/snake9_research.tex';new=p.read_text(encoding='utf-8')
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert editor.read_bytes()==p.read_bytes()
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
rx=r'\\begin\{(theorem|lemma|proposition|corollary|conjecture)\}(.*?)\\end\{\1\}'
norm=lambda t:re.sub(r'\s+',' ',t).strip()
statements=lambda t:Counter((k,norm(s)) for k,s in re.findall(rx,t,re.S))
assert not statements(old)-statements(new)
assert sum(statements(new).values())==sum(statements(old).values())+2
a=r'\section{Explicit transition sequences and blockers}';b=r'\begin{thebibliography}'
assert old[old.index(a):old.index(b)].strip()==new[new.index(a):new.index(b)].strip()
out=dict(status='PASSED',baseline=BASE,paper_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),editor_identical=True,preamble_preserved=True,old_statements_preserved=sum(statements(old).values()),added_statements=2,witness_appendix_unchanged=True,labels=len(labels),latex_compilation='Blocked before TeX by the Windows split-writable-root restricted-token runner; no rendered-page verification.')
(HERE/'data/paper-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
