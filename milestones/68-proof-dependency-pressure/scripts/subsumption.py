from pathlib import Path
import collections,gzip,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def canon(w):
 names=list(dict.fromkeys(w));return tuple(names.index(x) for x in w)
def key(w,c):return min((canon(w),tuple(c)),(canon(w[::-1]),tuple(c[::-1])))
def parse(rows):return {key(w,[lo for lo,hi in bounds]) for w,bounds in rows}
b=parse(read(R/'milestones/54-share-coverage/data/keys_235.json')['keys']);a=parse(read(R/'milestones/54-share-coverage/data/combined-keys.json')['keys']);assert b<=a
kept=set(b);needed=[];derived=[]
for w,c in sorted(a-b,key=lambda k:(len(k[1]),k)):
 hits=[]
 for width in range(2,len(c)):
  for start in range(len(c)-width+1):
   sub=key(w[start:start+width+1],c[start:start+width])
   if sub in kept:hits.append((width,start,sub))
 if hits:
  width,start,sub=min(hits);derived.append(dict(directions=w,counts=c,offset=start,premise=sub))
 else:kept.add((w,c));needed.append((w,c))
# Independent exhaustive membership comparison on all catalogue keys.
assert all(k in kept or any(key(k[0][j:j+width+1],k[1][j:j+width]) in kept for width in range(2,len(k[1])) for j in range(len(k[1])-width+1)) for k in a)
out=dict(total_keys=len(a),certified_reference_keys=len(b),remaining_keys=len(needed),derived_keys=len(derived),remaining_by_width=dict(collections.Counter(len(c) for w,c in needed)),needed=needed,derived=derived,scope='Exact contiguous-subwindow subsumption relative to the recorded 1287-key reference. Unproved remaining keys still require certificates or mathematical proofs; this is not a proof that the keys are true.')
(H/'data/count-subsumption.json.gz').write_bytes(gzip.compress(json.dumps(out,separators=(',',':')).encode(),mtime=0))
summary={k:v for k,v in out.items() if k not in ['needed','derived']}
(H/'data/count-subsumption-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary)
