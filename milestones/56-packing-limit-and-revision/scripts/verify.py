"""Check source preservation, all printed paths, and the zero-credit cycle."""
from pathlib import Path
import hashlib,itertools,json,re,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
BASE='c62466095bbbda5c79163364eadffc6e98d91a7c'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paper=ROOT/'paper/snake9_research.tex'
new=paper.read_text(encoding='utf-8')
old=subprocess.check_output(['git','-c','core.commitGraph=false','show',BASE+':paper/snake9_research.tex'],cwd=ROOT).decode().replace('\r\n','\n')
assert paper.read_bytes()==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
assert old.split(r'\begin{abstract}')[0]==new.split(r'\begin{abstract}')[0]
pattern=r'\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}.*?\\end\{\1\}'
statements=[m.group() for m in re.finditer(pattern,old,re.S)]
for statement in statements:
    expected=statement.replace(r'\boxed{191\le a(9)\le236.}',r'\boxed{191\le a(9)\le235.}')
    assert expected in new,statement[:100]
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
assert quotes(old)==quotes(new)
settings=[(9,0,191),(9,193,143),(9,77,138),(9,0,93),(8,0,98),(9,145,137),(8,0,96),(8,0,94)]
extra=json.loads((ROOT/'milestones/46-endpoint-paper-rewrite/data/new-witnesses.json').read_text())
settings += [(9,r['start_vertex'],r['edges']) for r in extra]
assert len(quotes(new))==len(settings)==11
pairs=0
def check_path(vs,n):
    assert len(set(vs))==len(vs) and all(0<=v<2**n for v in vs)
    for j in range(len(vs)):
        for i in range(j):assert ((vs[i]^vs[j]).bit_count()==1)==(j-i==1)
    return len(vs)*(len(vs)-1)//2
for text,(n,start,length) in zip(quotes(new),settings):
    ds=[int(x) for x in re.findall(r'\d',text)]
    assert len(ds)==length and max(ds)<n
    vs=[start]
    for d in ds:vs.append(vs[-1]^(1<<d))
    pairs+=check_path(vs,n)
block=new.split(r'\label{app:return-witnesses}')[1].split(r'\section{Finite verification')[0]
lists=re.findall(r'\\begin\{gathered\}(.*?)\\end\{gathered\}',block,re.S)
assert len(lists)==2
for text,folder,name,r,offsets,counts,shape in zip(lists,
    ['49-six-direction-pair-catalogue','50-three-count-return'],['witness-return.json','witness.json'],
    [95,64],[[1,3],[1,4,5]],[[2,3],[3,5,5]],[[0,1,2,0],[0,1,2,3,4,0]]):
    vs=list(map(int,re.findall(r'\d+',text)))
    recorded=json.loads((ROOT/'milestones'/folder/'data'/name).read_text())
    assert vs==recorded['vertex_sequence']
    pairs+=check_path(vs,9)
    S=set(vs)
    alpha=[sum(all(w not in S for w in [vs[r+k]^(1<<a),vs[r+k]^(1<<b),vs[r+k]^(1<<a)^(1<<b)]) for a,b in itertools.combinations(range(9),2)) for k in offsets]
    assert alpha==counts
    ds=[(vs[i]^vs[i+1]).bit_length()-1 for i in range(r,r+len(shape))]
    mapping={d:j for j,d in enumerate(dict.fromkeys(ds))}
    assert [mapping[d] for d in ds]==shape

# Check the cycle against the actual graph arrays rather than its prose summary.
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
np=model.np
record=json.loads((HERE/'data/zero-credit-cycle.json').read_text())
source=ROOT/record['source'];assert sha(source)==record['source_sha256']
analysis=json.loads(source.read_text());assert record['cycle']==analysis['cycle']
graph=source.parents[1]/'build/graph.npz'
meta=json.loads((source.parent/'model.json').read_text())
with np.load(graph) as z:arrays={k:z[k] for k in z.files}
for key,digest in meta['arrays_sha256'].items():assert hashlib.sha256(arrays[key].tobytes()).hexdigest()==digest
counts=[]
for j,e in enumerate(record['cycle']):
    assert e['next_state']==record['cycle'][(j+1)%25]['state']
    ix=np.flatnonzero((arrays['U']==e['state'])&(arrays['V']==e['next_state']))
    matches=[]
    for i in ix:
        cs=[int(arrays['count_code'][i])//6**k%6+1 for k in range(5,-1,-1)]
        ds=meta['extensions'][int(arrays['direction'][i])]
        if cs==e['counts'] and ds==e['directions']:matches.append(int(i))
    assert matches
    for i in matches:assert int(arrays['share_lower'][i])==e['share_lower']==0 and int(arrays['count'][i])==e['counts'][-1]
    counts.append(e['counts'][-1])
assert len(counts)==25 and sum(counts)==102 and counts==record['counts']
lean=json.loads((HERE/'data/lean-check.json').read_text())
assert {r['source'] for r in lean['records']}=={p.name for p in (HERE/'lean').glob('*.lean')}
audits=[]
for r in lean['records']:
    assert r['exit_code']==0 and r['sha256']==sha(HERE/'lean'/r['source'])
    assert (Path(lean['build'])/Path(r['source']).with_suffix('.olean')).is_file()
    log=(HERE/'logs'/Path(r['source']).with_suffix('.log')).read_text(encoding='utf-8')
    assert 'error:' not in log
    entries=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    assert len(entries)==5
    for name,axioms in entries:
        assert {a.strip() for a in axioms.split(',')}<={'propext','Classical.choice','Quot.sound'}
        audits.append(name)
out=dict(status='PASS',baseline_commit=BASE,paper_sha256=sha(paper),
    prior_statements=len(statements),prior_statements_preserved_except_updated_main_bound=True,
    current_statements=len(list(re.finditer(pattern,new,re.S))),labels=len(labels),
    printed_snakes=13,vertex_pair_checks=pairs,metadata_preserved=True,editor_identical=True,
    references_resolved=True,zero_credit_cycle_edges=25,zero_credit_count_sum=102,
    graph_arrays_hashes_checked=True,lean_modules=len(lean['records']),lean_audits=len(audits),
    scope='Source structure, printed constructions, exact graph cycle and new Lean arithmetic. No fresh complete rebuild of the contributor 235 proof; PDF compilation remains an independent check.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
