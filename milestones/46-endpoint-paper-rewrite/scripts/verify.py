"""Verify retained statements, references, metadata, and all printed witnesses."""
from pathlib import Path
import hashlib,itertools,json,re,subprocess
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
BASE='c0a672d7d314317bf69332fc7029e00853e16b04'
paper=ROOT/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
old=subprocess.check_output(['git','show',BASE+':paper/snake9_research.tex'],cwd=ROOT).decode().replace('\r\n','\n')
new=paper.read_text(encoding='utf-8')
assert paper.read_bytes()==editor.read_bytes()
assert old.split(r'\begin{abstract}')[0]==new.split(r'\begin{abstract}')[0]
pattern=r'\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}.*?\\end\{\1\}'
normalize=lambda s:re.sub(r'\\label\{[^}]*\}','',s)
statements=[normalize(m.group()) for m in re.finditer(pattern,old,re.S)]
for statement in statements:assert statement in normalize(new),statement[:100]
labels=re.findall(r'\\label\{([^}]+)\}',new)
assert len(labels)==len(set(labels))
assert set(re.findall(r'\\label\{([^}]+)\}',old))<=set(labels)
assert set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',new))<=set(labels)
cites={k for g in re.findall(r'\\cite\{([^}]+)\}',new) for k in g.split(',')}
assert cites<=set(re.findall(r'\\bibitem\{([^}]+)\}',new))
stack=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',new):
    if m[1]=='begin':stack.append(m[2])
    else:assert stack and stack.pop()==m[2],(m.start(),m[2])
assert not stack and '.lean' not in new
clean=re.sub(r'\\url\{[^}]*\}',r'\\url{URL}',new)
clean=re.sub(r'(?<!\\)%[^\n]*','',clean);clean=re.sub(r'\\[{}$%]','',clean)
level=0
for c in clean:
    if c=='{':level+=1
    elif c=='}':level-=1
    assert level>=0
assert level==0 and clean.count('$')%2==0
for a,b in [(r'\[',r'\]'),(r'\(',r'\)')]:assert clean.count(a)==clean.count(b)
catalogue=lambda s:s.split(r'\label{tab:exclusion-catalogue}')[1].split(r'\end{longtable}')[0]
assert catalogue(old)==catalogue(new)
quotes=lambda s:re.findall(r'\\begin\{quote\}\\small\\ttfamily\s*(.*?)\\end\{quote\}',s,re.S)
assert quotes(old)==quotes(new)[:8]
settings=[(9,0,191),(9,193,143),(9,77,138),(9,0,93),(8,0,98),(9,145,137),(8,0,96),(8,0,94)]
extra=json.loads((HERE/'data/new-witnesses.json').read_text())
settings += [(9,r['start_vertex'],r['edges']) for r in extra]
assert len(quotes(new))==len(settings)==11
pair_checks=0
for index,(text,(n,start,length)) in enumerate(zip(quotes(new),settings)):
    ds=[int(x) for x in re.findall(r'\d',text)]
    assert len(ds)==length and max(ds)<n
    vs=[start]
    for d in ds:vs.append(vs[-1]^(1<<d))
    assert len(set(vs))==len(vs)
    for j in range(len(vs)):
        for i in range(j):
            assert ((vs[i]^vs[j]).bit_count()==1)==(j-i==1)
            pair_checks+=1
    if index>=8:
        record=extra[index-8];assert vs==record['vertex_sequence']
        r=record['window_start'];positions=[r+1,r+5] if index==9 else [r+2,r+6]
        S=set(vs)
        alpha=[sum(all(w not in S for w in [vs[k]^(1<<a),vs[k]^(1<<b),vs[k]^(1<<a)^(1<<b)]) for a,b in itertools.combinations(range(9),2)) for k in positions]
        assert alpha==record['pair_counts']
        if index!=9:
            assert ds[r:r+8]==[0,1,2,3,4,0,3,1]
            assert [(vs[positions[0]]^v).bit_count() for v in [vs[0],vs[-1]]]==([2,4] if index==8 else [4,4])
        else:assert ds[r:r+6]==[0,1,2,3,4,2]
forest=lambda s:s.split(r'\subsection{A radius-three linear forest}')[1].split(r'\end{align*}')[0]
assert forest(old)==forest(new)
cycle_text=new.split(r'\label{app:replacement-cycle}')[1].split(r'\end{tabular}')[0]
rows=re.findall(r'^\d+ & \$\(([^)]+)\)\$ & \$\(([^)]+)\)\$\\\\$',cycle_text,re.M)
g=json.loads((ROOT/'milestones/44-critical-window-generalization/data/analysis.json').read_text())
assert len(rows)==len(g['cycle'])==11
for (d,c),r in zip(rows,g['cycle']):
    assert list(map(int,d.split(',')))==r['directions'] and list(map(int,c.split(',')))==r['counts']
assert sum(r['counts'][-1] for r in g['cycle'])==42
assert all(r['demand']==r['share_event']==0 for r in g['cycle'])
assert g['cycle'][4]['counts'][1]+g['cycle'][4]['counts'][5]==9
assert json.loads((ROOT/'milestones/45-pair-endpoint-demand/data/verification.json').read_text())['lean_audits']==16
out=dict(status='PASS',baseline_commit=BASE,prior_statements_preserved=len(statements),current_statements=len(list(re.finditer(pattern,new,re.S))),
    labels=len(labels),exclusion_rows=175,printed_snakes_rechecked=11,vertex_pairs_checked=pair_checks,new_pair_counts_and_endpoint_distances_checked=True,
    replacement_cycle_rows_checked=11,metadata_preserved=True,editor_identical=True,all_references_resolve=True,paper_sha256=hashlib.sha256(paper.read_bytes()).hexdigest(),
    scope='Source integrity and independent witness checks; not a fresh full rebuild of the archived 236 theorem or a visual page audit.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
