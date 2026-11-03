"""Bounded read-only reconstruction of the preserved146 semantic plan.

Writes only this audit directory; never imports a generator, invokes Lean, or
reads the large LRAT stream. Proof-variable completeness uses its pinned extractor.
"""
from pathlib import Path
from collections import Counter
import ast, datetime, hashlib, json, re, sys, types

sys.dont_write_bytecode=True
A=Path(__file__).resolve().parent; R=A.parents[2]
S=R/'milestones/146-initial-tree-and-paper'
P=R/'milestones/145-countfree-012301'
OLD=R/'milestones/72-four-count-proof-closure/critical-current'
UP=R/'milestones/28-direct-share-certificates/upstream'
pins={}
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def pin(p,expected=None):
    p=Path(p);d=sha(p)
    if expected is not None:assert d==expected,p
    pins[p.as_posix()]=d;return d
def cnf(p):
    lines=Path(p).read_text().splitlines()
    header=next(x.split() for x in lines if x.startswith('p '))
    cs=[list(map(int,x.split())) for x in lines if x and x[0] not in 'pc']
    assert all(x[-1]==0 for x in cs)
    cs=[x[:-1] for x in cs];assert len(cs)==int(header[3])
    return int(header[2]),cs

plan=read(S/'data/semantic-plan.json');sem=read(S/'data/share146.json')
replay=read(P/'data/direct-replay.json');conversion=read(P/'data/conversion-long.json')
assert replay['status']=='PASS_COMPLETE_DIRECT_RUP_REPLAY'
assert (replay['lemmas_checked'],replay['hints_checked'])==(285541,31017505)
assert replay['final_empty_clause'] and replay['every_derived_step_checked'] and replay['all_hint_identities_checked']
large=[]
for rel,d in plan['source_files_sha256'].items():
    p=R/rel
    if p.suffix=='.lrat':
        assert p.name=='trimmed.lrat' and p.stat().st_size==233402964
        assert d==replay['source_files_sha256'][str(p.relative_to(R))]
        large.append(dict(path=p.as_posix(),sha256_recorded=d,bytes=p.stat().st_size,
            independently_rehashed=False,reason='Pinned146 extraction and145 complete direct replay agree; large proof not reread'))
    else:pin(p,d)
for rel,d in replay['source_files_sha256'].items():
    p=R/rel
    if p.suffix!='.lrat':pin(p,d)
for item in plan['artifacts']:pin(S/item['path'],item['sha256'])
assert len(plan['artifacts'])==105
for p in [S/'data/semantic-plan.json',S/'data/share146.json',S/'data/native-reference.json',
          P/'data/proof-archives.json',Path(__file__)]:pin(p)
for name in ['LocalWindowModel','LocalWindowTags','LocalWindowTagsPacked',
             'LocalWindowShareModel','LocalWindowTagsShare','LocalWindowTagsSharePacked','LocalWindowBridge']:
    pin(UP/(name+'.lean'))
for name in ['LocalWindowModel','LocalWindowTags']:
    assert pin(R/'work/final_lean'/(name+'.lean'))==pins[(UP/(name+'.lean')).as_posix()]

meta=read(OLD/'data/pysat3-cap15-certificate.json')
assert meta['directions']==[0,1,2,3,0,1] and meta['bounds']==[[0,21]]*5 and meta['cap']==15
assert len(meta['cycle_cuts'])==16
def forbidden(*args,**kwargs):raise AssertionError('No solver allowed')
pysat=types.ModuleType('pysat');solvers=types.ModuleType('pysat.solvers')
solvers.Cadical153=forbidden;pysat.solvers=solvers
sys.modules.update({'pysat':pysat,'pysat.solvers':solvers})
sys.path.insert(0,str(R/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
import gen_lean_sat as gen
e=TaggedShare(meta['directions'],[(0,21)]*5,15,M=12)
for cc in meta['cycle_cuts']:e.add([-e.var[v] for v in cc],('old',('cut',)))
for name in ['tagged_share','gen_lean_sat','wincert']:pin(sys.modules[name].__file__)
nv,full=cnf(OLD/'build/pysat3-cap15.cnf')
assert nv==e.nv==11378 and len(full)==92656 and full==e.clauses
ids=read(P/'work/conversion-long/core-ids.json')
assert ids==sorted(set(ids)) and len(ids)==12977
assert ids==sem['source_original_clause_ids']
_,core=cnf(P/'work/conversion-long/core.cnf')
assert core==[full[k-1] for k in ids]
assert sem['core_ids']==list(range(1,12978))
assert sem['source_core_sha256']==pin(P/'work/conversion-long/core.cnf')
assert sem['source_full_sha256']==pins[(OLD/'build/pysat3-cap15.cnf').as_posix()]

proofvars=read(S/'data/proof-variables.json')
assert proofvars==sorted(set(proofvars)) and len(proofvars)==4219
corevars={abs(v) for c in core for v in c}
assert set(proofvars)<=corevars and len(corevars)==5323
active=corevars|set(proofvars);needed=set(active)
for lits,*_ in e.ctrs:needed.update(map(abs,lits))
for lits,*_ in e.tots:needed.update(map(abs,lits))
order=sorted(active)+sorted(needed-active)
ren={old:i+1 for i,old in enumerate(order)}
assert ren=={int(k):v for k,v in sem['original_to_new'].items()}
assert len(ren)==len(set(ren.values()))==5956 and set(ren.values())==set(range(1,5957))
assert sem['active_variables']==5323 and sem['semantic_variables']==5956
assert all(1<=ren[v]<=5323 for v in proofvars)
rl=lambda x:(1 if x>0 else -1)*ren[abs(x)]
code=lambda x:2*abs(rl(x))+(1 if x<0 else 0)
compact=[[rl(v) for v in c] for c in core]
cnv,cc=cnf(S/'certificates/share146.cnf')
assert cnv==5323 and cc==compact
pin(S/'certificates/share146.cnf')
inverse={v:k for k,v in ren.items()}
assert [[(1 if v>0 else -1)*inverse[abs(v)] for v in c] for c in compact]==core

cs=(S/'lean/LocalWindowCnf/ShareWindow146.lean').read_text()
assert 'def window : List Nat := [0, 1, 3, 7, 15, 14, 12]' in cs
assert 'def bounds : List (Nat × Nat) := [(0, 21), (0, 21), (0, 21), (0, 21), (0, 21)]' in cs
assert 'def resolution : Nat := 12' in cs and 'def cap : Nat := 15' in cs
rawchunks={int(i):ast.literal_eval(x) for i,x in re.findall(r'^def raw(\d+) : List \(List Nat\) := (.*)$',cs,re.M)}
assert list(rawchunks)==list(range(102)) and [len(rawchunks[i]) for i in range(102)]==[128]*101+[49]
raw=[[code(v) for v in c] for c in core]
assert sum(rawchunks.values(),[])==raw
data=(S/'lean/Share146/Data.lean').read_text()
tags=[e.tags[k-1] for k in ids]
def label(t):return '(.old '+gen.lean_tag(t[1])+')' if t[0]=='old' else gen.lean_tag(t)
taglines=dict((int(i),s) for i,s in re.findall(r'^def tags(\d+) : List TagS := (.*)$',data,re.M))
for i in range(102):assert taglines[i]=='['+','.join(map(label,tags[128*i:128*(i+1)]))+']'

# Independently decode the packed48/64-bit leaves for all renamed variables,
# including the dummy index0 and the semantic-only registers.
def leaves(r,s):
    if r+s>5956:return [r]
    return leaves(r,2*s)+leaves(r+s,2*s)
keys=leaves(0,1);assert len(keys)==5957 and set(keys)==set(range(5957))
packed48=int(re.search(r'def meaning : MT := \(mtB 5956 64 0 1 \(nat_lit 0x([0-9a-f]+)\)\)\.1',data).group(1),16)
packed64=int(re.search(r'def smeaning : MS := \(mtB64 5956 64 0 1 \(nat_lit 0x([0-9a-f]+)\)\)\.1',data).group(1),16)
decodedold={};decodedshare={}
for key in keys:
    x=packed48&((1<<48)-1);packed48>>=48
    if x&3==0:m=None
    elif x&3==1:m=('p',x>>2)
    elif x&3==2:m=('e',x>>2)
    else:m=('r',(x>>2)&255,(x>>10)&65535,x>>26)
    decodedold[key]=m
    x=packed64&((1<<64)-1);packed64>>=64
    if x&3==0:m=None
    elif x&3==1:m=('sq',(x>>2)&65535,(x>>18)&255,x>>26)
    elif x&3==2:m=('t',(x>>2)&1023,(x>>12)&65535,(x>>28)&65535,x>>44)
    else:m=('u',(x>>2)&65535,x>>18)
    decodedshare[key]=m
assert packed48==packed64==0
assert decodedold=={k:e.meaning.get(inverse.get(k)) for k in range(5957)}
assert decodedshare=={k:e.smeaning.get(inverse.get(k)) for k in range(5957)}

ct=[]
for lits,k,kind in e.ctrs:
    kt='.ends' if kind[0]=='ends' else f'(.{kind[0]} {kind[1]})'
    ct.append('⟨'+str([code(x) for x in lits])+f', {k}, {kt}⟩')
assert 'def ctrs : List Ctr := ['+','.join(ct)+']' in data
tt=[]
for lits,kind in e.tots:
    kt=f'(.{kind[0]} {kind[1]})' if kind[0]!='cap' else '(.cap '+str(kind[1])+')'
    tt.append('⟨'+str([code(x) for x in lits])+', '+kt+'⟩')
assert 'def tots : List Tot := ['+','.join(tt)+']' in data
assert len(e.ctrs)==1 and len(e.tots)==71

cycles=[];allcuts=[]
for index,(cid,tag,cl) in enumerate(zip(ids,tags,raw)):
    if tag!=('old',('cut',)):continue
    assert cl and all(v%2==1 and decodedold[v//2][0]=='p' for v in cl)
    verts=[decodedold[v//2][1] for v in cl]
    assert len(set(verts))==len(verts)
    nbr={v:[v^(1<<k) for k in range(9) if (v^(1<<k)) in verts] for v in verts}
    assert all(len(nbr[v])>=2 for v in verts)
    seen=set();stack=[verts[0]]
    while stack:
        v=stack.pop()
        if v not in seen:seen.add(v);stack.extend(nbr[v])
    allcuts.append(dict(original_clause_id=cid,size=len(verts),minimum_internal_degree=min(map(len,nbr.values()))))
    if cid>92640:
        assert verts==meta['cycle_cuts'][cid-92641]
        assert len(verts)==8 and seen==set(verts) and all(len(x)==2 for x in nbr.values())
        cycles.append(dict(original_clause_id=cid,input_cut_index_zero_based=cid-92641,
            compact_clause_id=index+1,shard=index//128,offset_zero_based=index%128,
            theorem='Snake9.LocalWindow.ShareWindow146.shard'+str(index//128),
            source=(S/f'lean/Share146/Shard{index//128:02d}.lean').as_posix(),
            vertices=verts,original_literals=core[index],renamed_literals=compact[index],
            encoded_literals=cl,tag='old/cut',minimum_internal_degree=2,connected=True,
            python_ckCut_conditions=True))
assert [x['original_clause_id'] for x in cycles]==[92641,92642,92643,92645,92648,92652]
assert [(x['shard'],x['offset_zero_based']) for x in cycles]==[(101,k) for k in range(43,49)]
shard=(S/'lean/Share146/Shard101.lean').read_text()
assert 'theorem shard101 : ckAllS meaning smeaning resolution ctrs tots window cap tags101 raw101 = true := by decide +kernel' in shard
assert len(allcuts)==259
for p,d in pins.items():assert sha(p)==d,('Changed during audit',p)
out=dict(status='PASS_BOUNDED_PRESERVED146_CORE_MAPPING_AND_CYCLE_INTERFACE_AUDIT',
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_files_sha256=pins,
    large_proof_pin_reused_without_rereading=large,
    parameters=dict(directions=[0,1,2,3,0,1],window=e.window,bounds=[[0,21]]*5,resolution=12,cap=15,radius=4),
    full_variables=11378,full_clauses=92656,core_clauses=12977,semantic_shards=102,last_shard_clauses=49,
    original_core_ids_exact=True,ordered_literals_exact=True,compact_ids=list(range(1,12978)),
    proof_variables=4219,proof_variables_all_in_original_core=True,
    every_listed_proof_variable_mapping=[[v,ren[v]] for v in proofvars],
    proof_renamed_min=min(ren[v] for v in proofvars),proof_renamed_max=max(ren[v] for v in proofvars),
    active_variables=5323,semantic_variables=5956,semantic_only_variables=633,
    renaming_bijection_checked=True,inverse_literal_reconstruction_checked=True,
    full_raw_chunks_and_tags_checked=True,packed_old_and_share_meanings_decoded=5957,
    endpoint_counters=1,share_totalizers=71,counter_and_totalizer_tables_exact=True,
    original_added_eight_cycle_cuts=16,retained_added_eight_cycle_cuts=cycles,
    all_retained_cycle_clauses=259,retained_cycle_sizes=dict(Counter(x['size'] for x in allcuts)),
    generic_acyclicity_suffices=True,
    generic_chain=['AxiomsS.toAxioms','Axioms.acyclic','Tags.sound_cut','Tags.sound_clause','Tags.sound_clauseS','Tags.sound_allS','Tags.soundS'],
    independent_checks=['Full original input reconstructed with the16 fixed cuts',
        'All12977 original clause IDs and literal order matched the145 core and146 export',
        'Every listed proof variable mapped by the exact active-first bijection',
        'All packed variable meanings and every raw/tag chunk reconstructed',
        'Every retained cycle clause checked against the degree condition of ckCut'],
    limitations=['No LRAT was reread or replayed. Completeness of the4219-variable list uses the pinned146 extractor against the proof pinned by145 complete replay.',
        'No Lean run. Shard101 is the designated checker, not a newly certified theorem in this audit.',
        'This audits preserved146 content. New147 import changes and fresh compiler receipts are outside the present result.',
        'A semantic composition theorem, consistently renamed complete contradiction replay, actual-snake geometry and reversal assembly remain separate.'],
    no_solver=True,no_lean=True,no_full_graph=True,no_original_writes=True)
target=A/'preserved146-review.json';assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],core_clauses=len(core),proof_variables=len(proofvars),
    active_variables=len(active),semantic_variables=len(ren),cuts=cycles,
    retained_cycle_sizes=out['retained_cycle_sizes'],receipt_sha256=sha(target)),indent=2))
