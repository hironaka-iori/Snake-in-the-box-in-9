from pathlib import Path
import collections,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def canon(ds):
 names=list(dict.fromkeys(ds));return tuple(names.index(x) for x in ds)
def key(row):
 ds,bs=row;b=tuple(map(tuple,bs));return min((canon(ds),b),(canon(ds[::-1]),b[::-1]))
base=read(R/'milestones/54-share-coverage/data/keys_235.json')['keys'];allkeys=read(R/'milestones/54-share-coverage/data/all-keys.json')['keys'];joint=read(R/'milestones/54-share-coverage/data/combined-keys.json')['keys']
b,a,j=map(lambda x:{key(r) for r in x},[base,allkeys,joint]);assert b<=a<=j
out=dict(base235_keys=len(b),all_known_keys=len(a),additional_control_keys=len(j-a),total_inherited_keys=len(j),keys_outside_base235=len(j-b),additional_keys_by_width=dict(collections.Counter(len(x[1]) for x in j-b)),inherited_share_rules=32,checked_oriented_share_rules=8,numerical_oriented_share_rules=24,
 count_status='The 1287-key contributor certificate set is reused; the remaining keys have numerical UNSAT provenance, without a complete proof inventory in this branch. Set difference does not assert that every additional key is logically independent.',
 files={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [R/'milestones/54-share-coverage/data/keys_235.json',R/'milestones/54-share-coverage/data/all-keys.json',R/'milestones/54-share-coverage/data/combined-keys.json',R/'milestones/57-replacement-share-family/combined/data/model.json']})
(H/'data/dependency-inventory.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
