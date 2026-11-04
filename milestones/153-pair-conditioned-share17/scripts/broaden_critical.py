"""Remove two unused lower-bound counters and verify the relabelled proof."""
from pathlib import Path
from collections import defaultdict,deque
import gzip,hashlib,importlib.util,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=H/'critical/work/critical17';D=H/'broader'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
assert not D.exists();D.mkdir()
activity=read(H/'data/counter-activity.json')
assert all(x['core_registers']==x['derived_registers']==0 for x in activity['rows'] if x['kind'] in [['lo',1],['lo',3]])
sys.path.insert(0,str(R/'milestones/28-direct-share-certificates/scripts'))
import tagged_share
old=tagged_share.TaggedShare([0,1,2,0,3,2],[(4,4),(4,4),(4,4),(5,5),(3,3)],16,M=12)
new=tagged_share.TaggedShare([0,1,2,0,3,2],[(4,4),(0,4),(4,4),(0,5),(3,3)],16,M=12)
dump=lambda e:(f'p cnf {e.nv} {len(e.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in e.clauses)).encode('ascii')
assert dump(old)==(P/'input.cnf').read_bytes()
old_base=max(old.meaning);new_base=max(new.meaning)
assert old.nv-old_base==new.nv-new_base
def meaning_key(e,m):
    if m[0]!='r':return tuple(m)
    return ('r',tuple(e.ctrs[m[1]][2]),m[2],m[3])
newmeaning={meaning_key(new,m):v for v,m in new.meaning.items()}
assert len(newmeaning)==len(new.meaning)
rename={v:newmeaning[meaning_key(old,m)] for v,m in old.meaning.items() if meaning_key(old,m) in newmeaning}
for v in range(old_base+1,old.nv+1):rename[v]=v-old_base+new_base
assert len(set(rename.values()))==len(rename)==new.nv
assert len(old.tots)==len(new.tots)
for v,m in old.smeaning.items():assert m==new.smeaning[rename[v]]
for (lits,*tail),(lits2,*tail2) in zip(old.tots,new.tots):
    assert tail==tail2 and [(1 if x>0 else -1)*rename[abs(x)] for x in lits]==lits2
remap=lambda row:[(1 if x>0 else -1)*rename[abs(x)] for x in row]
ids=read(P/'core-ids.json');lookup=defaultdict(deque)
for i,c in enumerate(new.clauses,1):lookup[tuple(c)].append(i)
input_id_map={}
for i in ids:
    mapped=tuple(remap(old.clauses[i-1]));assert lookup[mapped],i
    input_id_map[i]=lookup[mapped].popleft()
assert len(set(input_id_map.values()))==len(ids)
newids=sorted(input_id_map.values())
(D/'input.cnf').write_bytes(dump(new))
(D/'core-ids.json').write_text(json.dumps(newids)+'\n',encoding='utf-8')
(D/'core.cnf').write_text(f'p cnf {new.nv} {len(newids)}\n'+''.join(' '.join(map(str,new.clauses[i-1]))+' 0\n' for i in newids),encoding='ascii')
steps=0;hints=0
with (P/'trimmed.lrat').open(encoding='ascii') as src,(D/'trimmed.lrat').open('w',encoding='ascii',newline='\n') as out:
    for line in src:
        values=list(map(int,line.split()));z=values.index(0,1)
        cid=values[0];assert cid>len(old.clauses)>len(new.clauses)
        lits=remap(values[1:z]);hs=[input_id_map[h] if h<=len(old.clauses) else h for h in values[z+1:-1]]
        out.write(' '.join(map(str,[cid,*lits,0,*hs,0]))+'\n');steps+=1;hints+=len(hs)
assert (steps,hints)==(30305,1754767)
checker=R/'milestones/144-countfree-share18/scripts/certify_base.py'
spec=importlib.util.spec_from_file_location('broader_replay153',checker);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
start=time.monotonic();verified=module.replay(D/'trimmed.lrat',new.clauses,newids,steps,hints)
assert verified['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY'
oldmeta=read(H/'data/share153.json');oldcompact={int(k):v for k,v in oldmeta['original_to_new'].items()}
newcompact={rename[k]:v for k,v in oldcompact.items()}
compact=lambda row:[(1 if x>0 else -1)*newcompact[abs(x)] for x in row]
oldraw=[[int(x) for x in line.split()[:-1]] for line in (H/'certificates/share153.cnf').read_text().splitlines() if line and line[0] not in 'pc']
assert [compact(new.clauses[i-1]) for i in newids]==oldraw
meaning=D/'meanings.json.gz'
meaning.write_bytes(gzip.compress(json.dumps(dict(meaning=new.meaning,smeaning=new.smeaning,ctrs=new.ctrs,tots=new.tots,tags=new.tags,ball=new.ball,var=new.var)).encode(),mtime=0))
mapping=D/'mapping.json'
mapping.write_text(json.dumps(dict(variable_map=rename,input_clause_id_map=input_id_map,existing_compact_map=newcompact))+'\n',encoding='utf-8')
out=dict(status='PASS_BROADER_CONDITIONS_NATIVE_RUP_REPLAY',bounds=[[4,4],[0,4],[4,4],[0,5],[3,3]],
    removed_lower_bounds=[2,4],variables=new.nv,clauses=len(new.clauses),core_clauses=len(newids),
    deductions=steps,hints=hints,replay=verified,verification_seconds=time.monotonic()-start,
    compact_core_identical=True,no_new_solver_invocation=True,Lean_replay_complete=False,
    actual_snake_theorem_complete=False,new_global_upper_bound=False,
    source_files_sha256={str(p.relative_to(R)):sha(p) for p in [Path(__file__),Path(tagged_share.__file__),checker,
        P/'input.cnf',P/'trimmed.lrat',P/'core-ids.json',H/'data/counter-activity.json',H/'data/share153.json',
        D/'input.cnf',D/'core.cnf',D/'core-ids.json',D/'trimmed.lrat',meaning,mapping]},
    scope='The exact same contradiction has been replayed after removing two unused lower bounds and relabelling inputs. Compact core bytes agree. Broader clause semantics and the actual-snake adapter have not yet been generated or checked.')
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['source_files_sha256','replay']}))
