"""Resumable shared enumeration of five sufficient Q8 path-pair tasks."""
from pathlib import Path
import argparse,collections,hashlib,json,math,os,re,time
H=Path(__file__).resolve().parents[1]
N=[sum(1<<(v^(1<<k)) for k in range(8)) for v in range(256)]
C=[N[v]|(1<<v) for v in range(256)]
EVEN=sum(1<<v for v in range(256) if v.bit_count()%2==0)
def bits(mask):
    while mask:
        bit=mask&-mask;mask^=bit;yield bit.bit_length()-1
def mask(values):return sum(1<<v for v in set(values))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,j):
    t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');os.replace(t,p)
def induced(p):return len(p)==len(set(p)) and all(((u^p[j]).bit_count()==1)==(j==i+1) for i,u in enumerate(p) for j in range(i+1,len(p)))
def closed(p):
    out=0
    for v in p:out|=C[v]
    return out
def component(domain,u):
    reached=1<<u;todo=reached
    while todo:
        bit=todo&-todo;todo^=bit
        new=N[bit.bit_length()-1]&domain&~reached
        reached|=new;todo|=new
    return reached
def capacity(domain,u,v,edges):
    if not ((domain>>u)&1 and (domain>>v)&1):return 'ANCHOR',0
    comp=component(domain,u)
    if not (comp>>v)&1:return 'DISCONNECTED',comp
    if comp.bit_count()<edges+1:return 'SIZE',comp
    need=(edges+2)//2 if u.bit_count()%2==0 else (edges+1)//2
    if (comp&EVEN).bit_count()<need or (comp&~EVEN).bit_count()<edges+1-need:return 'COLOUR',comp
    return None,comp
def expand(p,domain,target,edges):
    current=p[-1];left=edges+1-len(p);dist=(current^target).bit_count()
    if left<0 or dist>left or (left-dist)%2:return None
    if current==target:return [] if left==0 else None
    if left==0:return None
    if (N[current]>>target)&1 and left!=1:return None
    available=domain&~closed(p[:-1])
    available|=1<<current
    reason,comp=capacity(available,current,target,left)
    if reason:return None
    choices=N[current]&comp&~mask(p)
    choices=choices&(1<<target) if left==1 else choices&~(1<<target)
    return [p+[v] for v in sorted(bits(choices),reverse=True)]

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--tag',required=True);ap.add_argument('--seconds',type=float,required=True)
ap.add_argument('--resume',type=Path);a=ap.parse_args()
assert re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]*',a.tag) and math.isfinite(a.seconds) and a.seconds>0
source=H/'data/companions.json';j=json.loads(source.read_bytes())
raw=json.loads((H/'data/regions44.json').read_bytes());seed=raw['seed']
assert len(seed)==192 and induced(seed)
for p,h in j['pins'].items():assert sha(p)==h
configs={c['id']:c for c in j['configurations']}
groups=collections.defaultdict(list)
for c in configs.values():
    key=(tuple(c['lower_anchors']),c['lower_edges'],tuple(c['lower_domain']),tuple(c['first_domain']))
    groups[key].append(c['id'])
assert list(groups.values())==[[0,2,4,6,8,10,12],[1,3,5,7,9,11,13],[14],[15],[16],[17]]
assert configs[17]['lower_anchors']==configs[0]['lower_anchors'] and configs[17]['lower_edges']==configs[0]['lower_edges']
assert set(configs[17]['lower_domain'])<=set(configs[0]['lower_domain']) and set(configs[17]['first_domain'])<=set(configs[0]['first_domain'])
representatives=[0,1,14,15,16]
tasks={}
for k in representatives:
    c=configs[k];u,v=c['lower_anchors']
    tasks[k]=dict(first=mask(c['first_domain'])&~(C[u]|C[v]),second=mask(c['lower_domain'])&~(C[18]|C[224]),u=u,v=v,edges=c['lower_edges'])
pins=dict(source=str(source),source_sha256=sha(source),script_sha256=sha(__file__),regions_sha256=sha(H/'data/regions44.json'),representatives=representatives)
state=dict(phase='first',first_frontier=[dict(path=[18],options=representatives)],second_frontier=[],pending_options=[])
counts=dict(first_prefixes=0,first_complete=0,second_prefixes=0,second_exhaustions=0,all_options_pruned=0,first_length_prunes=0,option_prunes={},first_complete_by_option={str(k):0 for k in representatives},max_first_edges=0)
prior=0.;resume=None
if a.resume:
    old=json.loads(a.resume.read_bytes());assert old['pins']==pins and old['status'] in ['TIME_LIMIT','INTERRUPTED','RUNNING']
    state=old['state'];counts=old['counts'];prior=old['cumulative_seconds'];resume=dict(path=str(a.resume.resolve()),sha256=sha(a.resume))
    assert state['phase'] in ['first','second'] and state['first_frontier']
    for x in state['first_frontier']:assert x['path'][0]==18 and len(x['path'])<=44 and induced(x['path']) and set(x['options'])<=set(representatives)
    if state['phase']=='second':
        assert len(state['first_frontier'][-1]['path'])==44 and state['first_frontier'][-1]['path'][-1]==224 and state['pending_options']
        t=tasks[state['pending_options'][0]]
        for p in state['second_frontier']:assert p[0]==t['u'] and len(p)<=t['edges']+1 and induced(p)
out=H/'data'/a.tag;out.mkdir(exist_ok=False)
start=time.monotonic();last=start;status='RUNNING';witness=None;error=None
def checkpoint():
    elapsed=time.monotonic()-start
    r=dict(status=status,pins=pins,resume=resume,counts=counts,seconds=elapsed,cumulative_seconds=prior+elapsed,witness=witness,error=error,exclusion=status=='EXHAUSTED',scope='Five representative Q8 pair tasks cover18 upper configurations in seven selected width44 contexts. Native enumeration, not a Lean traversal proof. A timeout implies no exclusion.')
    save(out/'checkpoint.json',dict(r,state=state))
    save(out/'result.json',dict(r,checkpoint_sha256=sha(out/'checkpoint.json'),pending_first_prefixes=len(state['first_frontier']),pending_second_prefixes=len(state['second_frontier'])))
def count_failure(reason):counts['option_prunes'][reason]=counts['option_prunes'].get(reason,0)+1
checkpoint()
try:
    while state['first_frontier']:
        now=time.monotonic()
        if now-start>=a.seconds:status='TIME_LIMIT';break
        if now-last>=5:checkpoint();last=time.monotonic()
        entry=state['first_frontier'][-1];p=entry['path']
        if state['phase']=='first':
            counts['first_prefixes']+=1;counts['max_first_edges']=max(counts['max_first_edges'],len(p)-1)
            used=mask(p);blocked=closed(p);options=[];union=0
            for k in entry['options']:
                t=tasks[k]
                if used&~t['first']:count_failure('FIRST_DOMAIN');continue
                reason,comp=capacity(t['second']&~blocked,t['u'],t['v'],t['edges'])
                if reason:count_failure(reason);continue
                options.append(k);union|=t['first']
            if not options:
                counts['all_options_pruned']+=1;state['first_frontier'].pop();continue
            children=expand(p,union,224,43)
            if children is not None and len(p)==44:
                counts['first_complete']+=1
                for k in options:counts['first_complete_by_option'][str(k)]+=1
                state.update(phase='second',pending_options=options,second_frontier=[[tasks[options[0]]['u']]])
            else:
                if children is None:counts['first_length_prunes']+=1
                state['first_frontier'].pop()
                state['first_frontier'].extend(dict(path=q,options=options) for q in children or [])
        else:
            k=state['pending_options'][0];t=tasks[k]
            if not state['second_frontier']:
                counts['second_exhaustions']+=1;state['pending_options'].pop(0)
                if state['pending_options']:state['second_frontier']=[[tasks[state['pending_options'][0]]['u']]]
                else:state['phase']='first';state['first_frontier'].pop()
                continue
            q=state['second_frontier'][-1];counts['second_prefixes']+=1
            domain=t['second']&~closed(p)
            children=expand(q,domain,t['v'],t['edges'])
            if children is not None and len(q)==t['edges']+1:
                c=configs[k];(left,right),(other,end)=c['intervals']
                first=p+[480];second=c['upper_prefix']+q+c['upper_suffix']
                full=seed[:left]+first+seed[right+1:other]+second+seed[end+1:]+[24]
                assert len(first)==len(second)==45 and induced(first) and induced(second)
                assert len(full)==193 and induced(full) and full[0]==0 and full[-1]==24
                assert sum((x^y)==256 for x,y in zip(full,full[1:]))==4
                witness=dict(config=k,context=c['context'],first_lower=p,second_lower=q,path=full,edges=192,pairwise_induced=True)
                status='WITNESS';break
            state['second_frontier'].pop();state['second_frontier'].extend(children or [])
    else:status='EXHAUSTED'
except KeyboardInterrupt:status='INTERRUPTED'
except Exception as e:
    status='ERROR';error=dict(type=type(e).__name__,message=str(e));raise
finally:checkpoint()
print(json.dumps(dict(status=status,result=str(out/'result.json'),counts=counts)),flush=True)
