"""Streaming preparation only; never invokes Lean, a solver, or subprocesses."""
from pathlib import Path
import argparse, collections, gzip, hashlib, heapq, json, math, time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
M145 = ROOT / 'milestones/153-pair-conditioned-share17'
M146 = M145
PROOF = M145 / 'critical/work/critical17/trimmed.lrat'
COREIDS = M145 / 'critical/work/critical17/core-ids.json'
FULL = M145 / 'critical/work/critical17/input.cnf'
META = M146 / 'data/share153.json'
CORE = M146 / 'certificates/share153.cnf'
OFF = 8192

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''): h.update(b)
    return h.hexdigest()

def save(p, obj):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, indent=2)+'\n', encoding='utf-8')

def rows(path=PROOF):
    with path.open('r', encoding='ascii') as f:
        for line in f:
            a = list(map(int, line.split()))
            if not a: continue
            z = a.index(0, 1)
            assert a[-1] == 0 and all(x > 0 for x in a[z+1:-1])
            yield a[0], a[1:z], a[z+1:-1]

def cnf(path):
    out = []
    for line in path.read_text(encoding='ascii').splitlines():
        if not line or line[0] in 'cp': continue
        a = list(map(int, line.split())); assert a[-1] == 0
        out.append(a[:-1])
    return out

def preorder(h):
    out = []
    def go(d,b):
        if d:
            k=b+(1<<(d-1));out.append(k);go(d-1,b);go(d-1,k)
    go(h,0)
    return out

def inspect():
    started=time.monotonic()
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in
          [PROOF,COREIDS,FULL,META,CORE,M145/'critical/work/critical17/native-replay.json']}
    assert pins[str(PROOF.relative_to(ROOT)).replace('\\','/')] == 'c3a7cb6b891cf7c2809a1d4702dce8cfd2a5611b823c350c1a6e3446f79e8b1b'
    meta=json.loads(META.read_text()); ids=json.loads(COREIDS.read_text())
    assert ids == meta['source_original_clause_ids']
    rename={int(k):v for k,v in meta['original_to_new'].items()}
    assert len(set(rename.values()))==len(rename)==6396
    original=cnf(FULL); compact=cnf(CORE)
    mapped=lambda c:[rename[abs(x)]*(1 if x>0 else -1) for x in c]
    assert compact==[mapped(original[i-1]) for i in ids]
    uses=collections.Counter();last={};rowmeta=[];seen=set(ids)
    totalh=0;totall=0;mh=0;ml=0;prev=len(original);active=set()
    for i,(cid,lits,hints) in enumerate(rows()):
        assert cid>prev and all(h in seen for h in hints)
        prev=cid;seen.add(cid);totalh+=len(hints);totall+=len(lits)
        mh=max(mh,len(hints));ml=max(ml,len(lits))
        active.update(abs(x) for x in lits)
        for x in lits: assert abs(x) in rename
        uses.update(hints)
        for h in hints:last[h]=i
        rowmeta.append([cid,len(lits),len(hints)])
    assert not lits and (len(rowmeta),totalh,len(ids))==(30305,1754767,11869)
    last[cid]=len(rowmeta)
    for c in ids:last.setdefault(c,-1)
    order=sorted(ids,key=lambda c:(-uses[c],c));slot={c:i+1 for i,c in enumerate(order)}
    initial=[slot[c] for c in ids]
    expire=collections.defaultdict(list)
    for c,i in last.items():expire[i].append(c)
    free=[];nxt=len(order)+1;alloc=[]
    for i,(cid,nl,nh) in enumerate(rowmeta):
        for c in expire.get(i,[]):heapq.heappush(free,slot[c])
        s=heapq.heappop(free) if free else nxt
        if s==nxt:nxt+=1
        slot[cid]=s;alloc.append(s)
        if cid not in last:heapq.heappush(free,s)
    h=(nxt-1).bit_length();keys=preorder(h);key={}
    for s,k in zip(initial,keys):key[s]=k
    unused=iter(keys[len(initial):])
    for s in range(1,nxt):
        if s not in key:key[s]=next(unused)
    width=max(h,(OFF+max(rename.values())+1).bit_length())
    segments=[];begin=0;nh=0
    for i,(_,_,n) in enumerate(rowmeta):
        nh+=n
        if nh>=6000 or i+1==len(rowmeta):segments.append([begin,i+1,nh]);begin=i+1;nh=0
    literalhex=math.ceil(width*(totall+totalh+3*len(rowmeta))/4)
    result={'status':'PASS_TRANSPORT_INPUTS_AND_BOUNDED_SIZE_PLAN','inputs':pins,
        'deductions':len(rowmeta),'hints':totalh,'core_clauses':len(ids),'clause_literals':totall,
        'max_clause_literals':ml,'max_hints_per_deduction':mh,'final_original_id':cid,
        'slot_count':nxt-1,'tree_height':h,'tree_nodes':len(keys),'word_width':width,
        'literal_offset':OFF,'segments':segments,'segment_count':len(segments),
        'packed_literal_hex_upper_bytes':literalhex,'seconds':time.monotonic()-started,
        'source_python_sha256':sha(Path(__file__)),'lean_invoked':False,'solver_invoked':False}
    assert ml<255 and mh<=4095, 'Existing checker fuel is insufficient'
    save(HERE/'data/sizing.json',result)
    save(HERE/'data/transport.json',{'source_original_clause_ids':ids,'original_to_new_variable':rename,
        'input_ordinal_to_slot':initial,'slot_to_tree_key':key,'deduction_slots':alloc,
        'last_use_step':last,'input_hint_rule':'Original retained input clause ID maps to compact 1-based ordinal; derived IDs stay unchanged before slot transport.',
        'slot_rule':'Hints read before clauses expiring at that step are overwritten; minimum freed slot reused.',
        'literal_rule':'Variable bijection preserves each sign, literal order, and multiplicity.'})
    print(json.dumps({k:v for k,v in result.items() if k not in ('inputs','segments')},indent=2),flush=True)
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('mode',choices=['inspect'])
    args=parser.parse_args();inspect()
