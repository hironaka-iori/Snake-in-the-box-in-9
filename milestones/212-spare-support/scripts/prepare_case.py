"""Bind the two spare-support families to the unchanged case-22 root model."""
from pathlib import Path
import itertools,json
from spare_continue import H,PREVIOUS,sha,save,engine_pins

folder=H/'data/case-22'
assert not folder.exists(), 'An existing research state must not be replaced.'
proof=json.loads((H/'data/SpareSupport212-audit.json').read_bytes())
assert proof['status']=='PASS'
assert sha(proof['source'])==proof['source_sha256']
row=next(r for r in json.loads((PREVIOUS/'data/six-coordinate-summary.json').read_bytes())['covered_records'] if r['index']==22)
original=PREVIOUS/row['folder']
assert sha(original/'model.json')==row['model_sha256']=='1a4d81c600d104347a501cfc9bf82db91a3aa04a6ebfd3ea20fcb1ca283aa95b'
m=json.loads((original/'model.json').read_bytes())
perms=json.loads((original/'permutations.json').read_bytes())
assert m['base']==[0,6] and len(m['block'])==6 and m['variables']==78 and len(perms)==120
record=next(r for r in json.loads((H/'data/square-capacity.json').read_bytes())['records'] if r['index']==22)
assert record['model_sha256']==row['model_sha256']
table={(c['x'],c['y']):c['rows'] for c in m['constraints']}
families=[];counts=[]
for parity,part in enumerate(record['parities']):
    clique=part['clique'];outside=part['outside'];partners=part['opposite_singleton_partners']
    words=sum(1<<u for u in range(64) if u.bit_count()%2==parity)
    assert len(set(clique))==len(clique) and len(set(outside))==len(outside)
    assert set(clique).isdisjoint(outside)
    assert set(clique+outside)==set(range(parity,m['variables'],2))
    assert set(map(int,partners))==set(outside)
    assert len(clique)==[30,26][parity] and len(outside)==[9,13][parity]
    assert all(m['domains'][x] and m['domains'][x]&~words==0 for x in clique+outside)
    for x in outside:
        ys=partners[str(x)]
        assert len(set(ys))==len(ys) and set(ys)<=set(clique)
    pairs=list(itertools.combinations(clique,2))+list(itertools.combinations(outside,2))
    pairs += [(x,y) for x in outside for y in clique if y not in partners[str(x)]]
    for x,y in pairs:
        rows=table[tuple(sorted((x,y)))]
        assert all(not(rows[u]>>u&1) for u in range(64) if words>>u&1)
    counts.append({'parity':parity,'clique':len(clique),'outside':len(outside),'spare':32-len(clique),'verified_pairs':len(pairs),'verified_equality_entries':32*len(pairs)})
    families.append({'clique':clique,'outside':outside,'partners':partners,'words':words})
assert sum(c['verified_equality_entries'] for c in counts)==41312
tail=[' '.join(map(str,[c['x'],c['y'],*c['rows']])) for c in m['constraints']]
tail+=[' '.join(map(str,v)) for v in m['nogoods']]+[' '.join(map(str,p)) for p in perms]
original_tail=('\n'.join(tail)+'\n').encode('ascii')
tail.append(str(len(families)))
for f in families:
    tail += [f'{len(f["clique"])} {f["words"]} {len(f["outside"])}',' '.join(map(str,f['clique']))]
    tail += [' '.join(map(str,[x,len(f['partners'][str(x)]),*f['partners'][str(x)]])) for x in f['outside']]
folder.mkdir()
for name in ['model.json','permutations.json']:(folder/name).write_bytes((original/name).read_bytes())
save(folder/'support-constraints.json',{'families':families,'model_sha256':row['model_sha256'],'scope':'Outside words are distinct; equality with a clique word is possible only at listed partners. At most 32-clique_count outside words are unshared.'})
(folder/'input-tail.txt').write_bytes(('\n'.join(tail)+'\n').encode('ascii'))
assert (folder/'input-tail.txt').read_bytes().startswith(original_tail)
names=['model.json','permutations.json','input-tail.txt','support-constraints.json']
state={'version':1,'index':22,'status':'OPEN','engine_pins':engine_pins(),'model_pins':{name:sha(folder/name) for name in names},'frontier':[{'id':0,'domains':m['domains']}],'next_id':1,'committed_jobs':0,'nodes':0,'seconds':0,'receipts':[]}
save(folder/'state.json',state);save(folder/'initial-state.json',state)
save(H/'data/root-preparation.json',{'status':'PREPARED','source_folder':str(original),'source_model_sha256':row['model_sha256'],'proof_audit_sha256':sha(H/'data/SpareSupport212-audit.json'),'families':counts,'initial_state_sha256':sha(folder/'initial-state.json'),'model_pins':state['model_pins'],'engine_pins':state['engine_pins'],'scope':'Complete unchanged source-model root. The earlier nonresumable limited run is not transferred. The appended support restrictions are logical consequences of the verified inequalities.'})
print(json.dumps({'status':'PREPARED','families':counts,'state_sha256':sha(folder/'state.json')},indent=2))
