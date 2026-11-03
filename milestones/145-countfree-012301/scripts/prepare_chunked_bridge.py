"""Preserve the stopped prototype and generate a sharded initial-tree bridge."""
from pathlib import Path
import ast, hashlib, json, re

H=Path(__file__).resolve().parents[1]; R=H.parents[1]
prototype=H/'lean/InputData145.lean'
literal=R/'milestones/144-countfree-share18/experiments/lean/LiteralData144.lean'
cnf=R/'milestones/144-countfree-share18/lean/LocalWindowCnf/ShareWindow144.lean'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=prototype.read_text()
definitions=re.findall(r'^def (part\d+|tree) : InputTree := (.*)$',source,re.M)
assert len(definitions)==105
parts={name:body for name,body in definitions}

def parse(body):
    toks=re.findall(r'InputTree\.\w+|part\d+|\d+|[()\[\],]',body); i=0
    def expr():
        nonlocal i
        t=toks[i];i+=1
        if t.startswith('part'):return ('part',t)
        if t=='InputTree.empty':return ('empty',)
        assert t=='('
        kind=toks[i];i+=1
        if kind=='InputTree.tautology':
            d,b=int(toks[i]),int(toks[i+1]);i+=2
            assert toks[i]==')';i+=1
            return ('tautology',d,b)
        assert kind=='InputTree.node'
        key=int(toks[i]);i+=1;assert toks[i]=='[';i+=1;cl=[]
        while toks[i]!=']':
            if toks[i]!=',':cl.append(int(toks[i]))
            i+=1
        i+=1; left=expr();right=expr();assert toks[i]==')';i+=1
        return ('node',key,cl,left,right)
    ans=expr();assert i==len(toks);return ans

trees={name:parse(body) for name,body in definitions}
def clauses(t):
    if t[0] in ('empty','tautology'):return []
    if t[0]=='part':return clauses(trees[t[1]])
    return [t[2]]+clauses(t[3])+clauses(t[4])

raw=[]
for text in re.findall(r'^def raw\d+ : List \(List Nat\) := (.*)$',cnf.read_text(),re.M):
    raw.extend(ast.literal_eval(text))
assert len(raw)==13224 and clauses(trees['tree'])==raw

def raw_expression(t):
    if t[0] in ('empty','tautology'):return '[]'
    if t[0]=='part':return t[1]+'.clauses'
    return f'({t[2]} :: ({raw_expression(t[3])} ++ {raw_expression(t[4])}))'

def build_expression(t):
    if t[0]=='empty':return 'Snake9.Lrat144.Tree.nil'
    if t[0]=='tautology':return f'(Snake9.LratFast144.perf {t[1]} {t[2]})'
    if t[0]=='part':return t[1]+'.build'
    return f'(Snake9.Lrat144.Tree.node {t[1]} (Snake9.Lrat144.rawMask {t[2]}) {build_expression(t[3])} {build_expression(t[4])})'

settings='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n'
namespace='namespace Snake9.ChunkData145\nopen Snake9.InputTree145 (InputTree)\n'
generated={}
def save(name,text):
    p=H/'lean'/(name+'.lean');assert not p.exists(),p
    p.write_text(text,encoding='utf-8',newline='\n');generated[name]=sha(p)

save('ChunkData145','import InputTree145\n'+settings+namespace+
    '\n'.join('def '+name+' : InputTree := '+body for name,body in definitions)+
    '\nend Snake9.ChunkData145\n')

shards=[]
for n in range(13):
    name=f'ChunkParts145{n:02d}';shards.append(name)
    text='import ChunkData145\nimport LiteralData144\n'+settings+namespace
    for i in range(8*n,8*n+8):
        text+=f'theorem part{i}_clauses : part{i}.clauses = {clauses(trees[f"part{i}"])} := by rfl\n'
        text+=f'theorem part{i}_build : part{i}.build = Snake9.LiteralData144.part{i} := by rfl\n'
        text+=f'#print axioms part{i}_clauses\n#print axioms part{i}_build\n'
    text+='end Snake9.ChunkData145\n';save(name,text)

text=''.join('import '+n+'\n' for n in shards)+'import LocalWindowCnf.ShareWindow144\n'+settings+namespace
text+='theorem tree_clauses_split : tree.clauses = '+raw_expression(trees['tree'])+' := by rfl\n'
text+='theorem tree_build_split : tree.build = '+build_expression(trees['tree'])+' := by rfl\n'
text+='theorem clauses_eq : tree.clauses = Snake9.LocalWindow.ShareWindow144.raw := by\n'
text+='  rw [tree_clauses_split, '+', '.join(f'part{i}_clauses' for i in range(104))+']\n  rfl\n'
text+='theorem materialized_eq : tree.build = Snake9.LiteralData144.start := by\n'
text+='  rw [tree_build_split, '+', '.join(f'part{i}_build' for i in range(104))+']\n  rfl\n'
text+='''theorem start_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow144.cnf = true) :
    Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.start := by
  rw [← materialized_eq]
  exact tree.start_true τ clauses_eq h
#print axioms tree_clauses_split
#print axioms tree_build_split
#print axioms clauses_eq
#print axioms materialized_eq
#print axioms start_true
end Snake9.ChunkData145
'''
save('ChunkAssembly145',text)
receipt=dict(status='PREPARED_CHUNKED_BRIDGE_CHECKS_PENDING',clauses=len(raw),parts=104,shards=13,
    part_clause_counts=[len(clauses(trees[f'part{i}'])) for i in range(104)],
    source_files_sha256={p.as_posix():sha(p) for p in [Path(__file__),prototype,literal,cnf,H/'lean/InputTree145.lean']},
    generated_sha256=generated,check_order=['ChunkData145']+shards+['ChunkAssembly145'],
    original_prototype_untouched=True,scope='Only preserved144 initial-tree truth bridge; no selected145 share theorem')
p=H/'data/chunked-bridge-preparation.json';assert not p.exists();p.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['status','clauses','parts','shards']}))
