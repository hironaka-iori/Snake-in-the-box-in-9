"""Check and pack every count-free150 RUP step, streaming bounded-memory data.

No Lean, solvers, subprocesses, or imports of dynamically generated proof code.
"""
from pathlib import Path
import gzip, hashlib, json, struct, time
import prepare_replay as p

def pack(words,width):
    x=0
    for w in reversed(words):
        assert 0<=w<(1<<width)
        x=(x<<width)|w
    return x

def unpack(x,width):
    out=[];mask=(1<<width)-1
    while x:out.append(x&mask);x>>=width
    return out

def bit(lit):return abs(lit)+(p.OFF if lit<0 else 0)
def cmask(lits):
    x=0
    for lit in lits:x|=1<<bit(lit)
    return x

def run():
    started=time.monotonic();s=json.loads((p.HERE/'data/sizing.json').read_text())
    t=json.loads((p.HERE/'data/transport.json').read_text())
    for rel,digest in s['inputs'].items():assert p.sha(p.ROOT/rel)==digest
    rename={int(k):v for k,v in t['original_to_new_variable'].items()}
    key={int(k):v for k,v in t['slot_to_tree_key'].items()}
    last={int(k):v for k,v in t['last_use_step'].items()}
    ids=t['source_original_clause_ids'];initial=t['input_ordinal_to_slot']
    alloc=t['deduction_slots'];width=s['word_width'];pre=p.preorder(s['tree_height'])
    core=p.cnf(p.CORE);idtoslot=dict(zip(ids,initial));owner=dict(zip(initial,ids))
    db={key[slot]:cmask(c) for slot,c in zip(initial,core)}
    entries={key[slot]:pack([bit(x)+1 for x in c],width) for slot,c in zip(initial,core)}
    expire={}
    for cid,i in last.items():expire.setdefault(i,[]).append(cid)
    checkpoint_dir=p.HERE/'data/checkpoints';checkpoint_dir.mkdir(parents=True,exist_ok=True)
    checkpoints=[];segdata=[];seg=0;segstart=0;segrefs=0;allrefs=0
    cp_hex_bytes=0;proof_hex_bytes=0;maxlive=len(ids);mapping_digest=hashlib.sha256()
    mapped_lrat=p.HERE/'data/renamed.lrat.gz';packed=p.HERE/'data/packed-steps.bin'
    indexout=p.HERE/'data/packed-index.jsonl.gz'
    def checkpoint(nextsegment,step):
        nonlocal cp_hex_bytes
        live={key[slot] for cid,slot in idtoslot.items() if last.get(cid,-1)>=step}
        values=[format(entries[k],'x') if k in live else '0' for k in pre]
        estimated=sum(len(x)+12 for x in values)
        cp_hex_bytes+=estimated
        target=checkpoint_dir/f'cp{nextsegment:05d}.json.gz'
        with gzip.open(target,'wt',encoding='ascii',compresslevel=1) as f:json.dump(values,f,separators=(',',':'))
        checkpoints.append({'before_segment':nextsegment,'after_step':step,'live_clauses':len(live),
            'path':str(target.relative_to(p.HERE)).replace('\\','/'),'sha256':p.sha(target),
            'lean_literal_upper_bytes':estimated})
    with packed.open('wb') as out,gzip.open(mapped_lrat,'wt',encoding='ascii',compresslevel=1) as tr,gzip.open(indexout,'wt',encoding='ascii',compresslevel=1) as ix:
        for i,(cid,lits,hints) in enumerate(p.rows()):
            ml=[rename[abs(x)]*(1 if x>0 else -1) for x in lits]
            slots=[idtoslot[h] for h in hints]
            for h,slot in zip(hints,slots):assert owner[slot]==h
            hs=[key[x] for x in slots];dest=key[alloc[i]]
            words=[dest]+[bit(x)+1 for x in ml]+[0]+hs
            x=pack(words,width)
            assert unpack(x,width)==words, f'word roundtrip {i}'
            decoded=unpack(x,width);zpos=decoded.index(0,1)
            clausebits=[v-1 for v in decoded[1:zpos]]
            assert clausebits==[bit(l) for l in ml] and decoded[zpos+1:]==hs
            z=0
            for b in clausebits:z|=1<<b
            conflict=False
            for k in decoded[zpos+1:]:
                assert k in db
                if conflict:continue
                u=db[k]&~z
                if u==0:conflict=True
                elif u&(u-1)==0:
                    b=u.bit_length()-1;z|=1<<(b-p.OFF if b>=p.OFF else b+p.OFF)
                else:raise AssertionError(f'non-unit packed hint at step {i}, key {k}')
            assert conflict, f'no conflict in step {i}'
            payload=x.to_bytes((x.bit_length()+7)//8,'little');offset=out.tell()
            out.write(struct.pack('<I',len(payload)));out.write(payload)
            ix.write(json.dumps([i,cid,alloc[i],dest,offset,len(payload),len(lits),len(hints)],separators=(',',':'))+'\n')
            proof_hex_bytes+=len(format(x,'x'))+12
            # Independent visible clause-ID transport keeps all original derived IDs.
            if i==0:inputmap={c:j+1 for j,c in enumerate(ids)}
            ch=[inputmap.get(h,h) for h in hints]
            tr.write(' '.join(map(str,[cid,*ml,0,*ch,0]))+'\n')
            mapping_digest.update(struct.pack('<QQ',cid,dest))
            for h,k in zip(hints,hs):mapping_digest.update(struct.pack('<QQ',h,k))
            for old in expire.get(i,[]):
                slot=idtoslot.pop(old);owner.pop(slot)
            slot=alloc[i];assert slot not in owner
            idtoslot[cid]=slot;owner[slot]=cid;db[dest]=cmask(ml)
            entries[dest]=pack([bit(l)+1 for l in ml],width)
            if cid not in last:idtoslot.pop(cid);owner.pop(slot)
            maxlive=max(maxlive,len(idtoslot));allrefs+=len(hints);segrefs+=len(hints)
            if i+1==s['segments'][seg][1]:
                segdata.append({'segment':seg,'first_step':segstart,'after_step':i+1,
                    'hints':segrefs,'packed_after_byte':out.tell()})
                seg+=1;segstart=i+1;segrefs=0
                if seg==1 or (seg%32==0 and seg<s['segment_count']):checkpoint(seg,i+1)
            if i%25000==0:print(f'packed checked {i+1}/58182 steps, {allrefs} hints',flush=True)
        assert i+1==58182 and allrefs==5350080 and ml==[] and db[dest]==0
    for rel,digest in s['inputs'].items():assert p.sha(p.ROOT/rel)==digest
    artifacts=[packed,mapped_lrat,indexout]
    receipt={'status':'PASS_COMPLETE_RENAMED_AND_PACKED_RUP_REPLAY','deductions':i+1,
        'hints':allrefs,'final_original_clause_id':cid,'final_tree_key':dest,'final_empty':True,
        'segments':segdata,'checkpoint_interval_segments':32,'checkpoints':checkpoints,
        'word_width':width,'literal_offset':p.OFF,'tree_height':s['tree_height'],'max_live_clauses':maxlive,
        'packed_source_hex_bytes':proof_hex_bytes,'checkpoint_source_hex_upper_bytes':cp_hex_bytes,
        'all_hints_and_literals_preserved':True,'transport_pair_sha256':mapping_digest.hexdigest(),
        'input_receipt_sha256':p.sha(p.HERE/'data/sizing.json'),'mapping_sha256':p.sha(p.HERE/'data/transport.json'),
        'artifacts':[{'path':str(x.relative_to(p.HERE)).replace('\\','/'),'sha256':p.sha(x),'bytes':x.stat().st_size} for x in artifacts],
        'source_python_sha256':p.sha(Path(__file__)),'seconds':time.monotonic()-started,
        'lean_invoked':False,'solver_invoked':False,
        'limitation':'Python verification is complete; Lean kernel replay remains pending.'}
    p.save(p.HERE/'data/packed-replay.json',receipt)
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('segments','checkpoints')},indent=2),flush=True)

if __name__=='__main__':run()
