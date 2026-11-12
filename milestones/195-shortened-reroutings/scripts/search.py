"""Explore induced block reroutings and endpoint additions from the shortened bank.

COMPLETE means the full reachable queue was exhausted for this move rule.
Interrupted current states are recorded separately and never counted complete.
"""
from pathlib import Path
import argparse, collections, datetime, hashlib, json, time
from native_resources import snapshot

H=Path(__file__).resolve().parents[1]; R=H.parents[1]
ap=argparse.ArgumentParser()
ap.add_argument('--max-block',type=int,default=8)
ap.add_argument('--seconds',type=float,default=180)
ap.add_argument('--max-states',type=int,default=10000)
ap.add_argument('--tag',default='closure8')
ap.add_argument('--input',default='')
a=ap.parse_args(); assert 2<=a.max_block<=40
dest=H/'data'/(a.tag+'.json'); assert not dest.exists()
gate=snapshot(); assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=R/'milestones/193-block-reroutings/data/shorten2-blocks4-24.json'
regrowth=source.with_name('regrowth.json'); bankpath=R/'work/bank9.json'
raw=source.read_bytes(); data=json.loads(raw); assert data['status']=='COMPLETE'
growth=json.loads(regrowth.read_bytes()); assert growth['source_sha256']==hashlib.sha256(raw).hexdigest()
bankraw=bankpath.read_bytes(); bank=json.loads(bankraw)
N=[[v^(1<<k) for k in range(9)] for v in range(512)]
NM=[sum(1<<w for w in ns) for ns in N]

def canonical(p):
    trans=[(u^v).bit_length()-1 for u,v in zip(p,p[1:])]
    def rename(xs):
        names={}; out=[]
        for x in xs:
            if x not in names: names[x]=len(names)
            out.append(names[x])
        return tuple(out)
    return min(rename(trans),rename(trans[::-1]))

def valid(p):
    seen=0
    for i,v in enumerate(p):
        if (seen>>v)&1: return False
        if NM[v]&seen != (0 if i==0 else 1<<p[i-1]): return False
        seen|=1<<v
    return True

known={canonical(row['vertex_sequence']):i for i,row in enumerate(bank)}
states=[]; classes={}; current=None; complete=[]; nodes=0; moves=0
started=time.monotonic(); resource_samples=[]; witness=None
class Stop(Exception): pass

def budget():
    if time.monotonic()-started>a.seconds: raise Stop('TIME_LIMIT')
    if not resource_samples or time.monotonic()-started-resource_samples[-1]['elapsed']>5:
        s=snapshot(); s['elapsed']=time.monotonic()-started; resource_samples.append(s)
        if s['errors'] or s['processes'] or s['free_bytes']<768*1024**2: raise Stop('RESOURCE_LIMIT')

def add(p,parent,operation):
    global witness
    code=canonical(p)
    if code in classes: return classes[code],False
    assert valid(p)
    if len(states)>=a.max_states: raise Stop('STATE_LIMIT')
    idx=len(states); classes[code]=idx
    record=dict(path=p,parent=parent,operation=operation,bank191_class=known.get(code))
    states.append(record)
    if len(p)>=193: witness=idx; raise Stop('LONGER_WITNESS_FOUND')
    return idx,True

priority=sorted(range(len(data['new_classes'])),key=lambda i:(-growth['rows'][i]['maximum_added_edges'],i))
for i in priority:
    add(data['new_classes'][i]['path'],None,dict(kind='shortened_seed',source_class=i))
inputs={str(source):hashlib.sha256(raw).hexdigest(),str(regrowth):hashlib.sha256(regrowth.read_bytes()).hexdigest(),str(bankpath):hashlib.sha256(bankraw).hexdigest()}
if a.input:
    prior=H/'data'/a.input; priorraw=prior.read_bytes(); prev=json.loads(priorraw)
    inputs[str(prior)]=hashlib.sha256(priorraw).hexdigest()
    for i,row in enumerate(prev['states']): add(row['path'],None,dict(kind='previous_run_state',source=str(prior),source_state=i))

def save(status):
    out=dict(status=status,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),arguments=vars(a),
        inputs=inputs,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        seconds=time.monotonic()-started,resource_gate=gate,resource_samples=resource_samples,
        nodes=nodes,moves=moves,completed_states=complete,current_incomplete=current if status!='COMPLETE' else None,
        states=states,counts_by_edges=dict(collections.Counter(len(s['path'])-1 for s in states)),
        new191_states=[i for i,s in enumerate(states) if len(s['path'])==192 and s['bank191_class'] is None],witness=witness,
        scope='All same-length contiguous replacements of 2..max_block edges, and one-edge additions at either endpoint, iterated by a queue of cube-isometry/reversal classes. No shortening after the initial seeds.')
    dest.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf-8')

try:
    cursor=0
    while cursor<len(states):
        p=states[cursor]['path']; current=dict(state=cursor,blocks_complete=0,endpoint_moves=0,routes=0,new_states=0)
        budget()
        for rev in [False,True]:
            oriented=p[::-1] if rev else p
            seen=sum(1<<z for z in oriented)
            for w in N[oriented[-1]]:
                if not (seen>>w)&1 and NM[w]&seen==1<<oriented[-1]:
                    _,fresh=add(oriented+[w],cursor,dict(kind='endpoint',reversed=rev,vertex=w))
                    current['endpoint_moves']+=1; current['new_states']+=fresh
        for length in range(2,a.max_block+1):
            for i in range(len(p)-length):
                budget(); j=i+length; u=p[i]; v=p[j]
                current['active_block']=[i,j]
                retained=p[:i+1]+p[j:]
                forbidden=sum(1<<z for z in retained)
                for z in retained:
                    if z!=u and z!=v: forbidden|=NM[z]
                route=[u]
                def dfs(left,blocked):
                    global nodes,moves
                    nodes+=1
                    if nodes%2048==0: budget()
                    last=route[-1]; distance=(last^v).bit_count()
                    if distance>left or (left-distance)%2: return
                    if left==1:
                        if v not in N[last] or (blocked>>v)&1: return
                        current['routes']+=1
                        if route[1:]==p[i+1:j]: return
                        moves+=1
                        q=p[:i]+route+p[j:]
                        assert len(q)==len(p)
                        _,fresh=add(q,cursor,dict(kind='block',start=i,end=j,interior=route[1:]))
                        current['new_states']+=fresh
                        return
                    excluded=blocked|forbidden|(1<<v)
                    for w in N[last]:
                        if (excluded>>w)&1: continue
                        route.append(w); dfs(left-1,blocked|NM[last]|(1<<last)); route.pop()
                dfs(length,0)
                current['blocks_complete']+=1
        current.pop('active_block',None); complete.append(current); current=None; cursor+=1
        if cursor%25==0:
            print(json.dumps(dict(completed=cursor,states=len(states),counts=dict(collections.Counter(len(s['path'])-1 for s in states)),seconds=round(time.monotonic()-started,3))),flush=True)
    status='COMPLETE'
except Stop as stop: status=str(stop)
save(status)
print(json.dumps(dict(status=status,completed=len(complete),states=len(states),witness=witness,seconds=round(time.monotonic()-started,3),file=str(dest))),flush=True)
