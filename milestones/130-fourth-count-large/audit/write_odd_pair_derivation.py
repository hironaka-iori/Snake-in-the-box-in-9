"""Record the checked parity strengthening and its exact dependency evidence."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
rows=[];pins={}
for module,kind,checker,count in [('DfsParity','parity-dependency','check_parity_dependency.py',4),
                                  ('OddPair130','odd-pair','check_odd_pair.py',8)]:
 rp=H/'data'/f'independent-{kind}-audit.json';q=read(rp)
 assert q['status']=='PASS' and q['exit_code']==0 and not q.get('timeout',False) and q['dependencies_unchanged']
 for name,digest in q['dependencies'].items():assert sha(name)==digest,name
 source=H/'lean'/(module+'.lean');check=H/'audit'/checker;log=Path(q['log'])
 assert sha(source)==q['source_sha256']==q['source_current_sha256']==sha(log.parent/'source.lean.txt')
 assert sha(check)==q['checker_sha256']==q['checker_current_sha256']==sha(log.parent/'checker.py.txt')
 for name in ['object','importable_object','log']:assert sha(q[name])==q[name+'_sha256']
 assert len(q['axioms'])==count and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.read_text())
 for p in [rp,source,check,log,Path(q['object']),Path(q['importable_object']),log.parent/'record.json',
           log.parent/'source.lean.txt',log.parent/'checker.py.txt']:
  pins[p.relative_to(H).as_posix()]=sha(p)
 rows.append(dict(module=module,receipt=rp.relative_to(H).as_posix(),source_sha256=sha(source),
                  object_sha256=q['importable_object_sha256'],receipt_sha256=sha(rp),
                  seconds=q['seconds'],axioms=q['axioms']))
assert (H/'lean/DfsParity.lean').read_bytes()==(R/'work/final_lean/DfsParity.lean').read_bytes()
pins['audit/parity-source-copy.json']=sha(H/'audit/parity-source-copy.json')
pins['audit/write_odd_pair_derivation.py']=sha(Path(__file__))
out=dict(status='PASS_ACTUAL_PARITY_PAIR_NINE',new_module='OddPair130',new_axiom_reports=8,
         exact_rebuilt_dependency='DfsParity',dependency_axiom_reports=4,
         equality_forces_even_length=True,equality_forces_even_start=True,
         pair_lower_nine_when_length_or_start_odd=True,length235_specialization_checked=True,
         new_global_upper_bound=False,reports=rows,pins=pins,
         scope='Actual fitting canonical012032 windows. Pair sum8 implies even m and r. Pair sum>=9 holds if m or r is odd, including all such windows in length235. No global upper bound follows without the counting/graph argument.')
vf=H/'data/odd-pair-verification.json';assert not vf.exists();vf.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
note=r'''# Pair equality requires even length and an even start

Lean checks the following statements for an actual induced path
\(p_0,\ldots,p_m\) in \(Q_9\). Let \(r+6\le m\), and suppose the six
directions starting at \(r\) have canonical word \(012032\). Then

\[
\alpha_{r+2}+\alpha_{r+4}=8
\quad\Longrightarrow\quad
m\equiv0\pmod2\ \text{and}\ r\equiv0\pmod2.
\]

Combining this with the proved pair lower bound eight gives

\[
\alpha_{r+2}+\alpha_{r+4}\ge9
\quad\text{if }m\equiv1\pmod2\ \text{or }r\equiv1\pmod2.
\]

In particular, every fitting canonical \(012032\) window in a snake of
235 edges satisfies the pair lower bound nine. The start index is the
existing zero-based path index: the relevant centres occur at positions
\(r+2\) and \(r+4\).

## Argument

The completed endpoint theorem states that pair equality places both centres
at Hamming distance two from both endpoints. Vertices at Hamming distance
two have the same parity of the number of one coordinates. Thus the centre
at position \(r+2\) has the same parity as \(p_0\), which forces \(r+2\)
and hence \(r\) to be even. Both endpoints also have the same parity, which
forces \(m\) to be even because each path edge reverses parity.

The existing pair theorem gives a sum at least eight. If either length or
start is odd, the equality case is impossible. The sum is an integer, so it
is at least nine. The specialization to 235 uses its odd parity directly.

The proof uses a generic list induction showing that the parity of an XOR
count is the parity of the sum of the two counts. This yields the XOR rule
for vertex parity and then the distance-two parity statement. It does not
enumerate triples of cube vertices. No new mathematical definition is
introduced.

## Checked statements and evidence

`OddPair130` passed eight printed axiom reports in ODD_SECONDS seconds:

- parity of a generic XOR count;
- parity of the XOR of two vertices;
- equality of vertex parity at Hamming distance two;
- even length and start forced by actual pair equality;
- pair lower bound nine when the length or start is odd;
- its odd-length and odd-start specializations;
- its length-235 specialization.

Every report contains only a subset of `propext`, `Classical.choice` and
`Quot.sound`. The source contains no omitted proof or native-decide step.

The earlier `DfsParity` verification recorded source and theorem audits but
did not bind the current compiled object to that invocation. An exact byte
copy of `work/final_lean/DfsParity.lean` was therefore rebuilt in this
milestone. Its four existing reports passed in DEP_SECONDS seconds. The new
proof resolves that rebuilt object first. Its endpoint and pair objects
match the hashes in the completed milestone-122 audit saved in milestone 129.

Both compiler checks used the required fresh resource gate and a bounded
600-second allowance. Source snapshots, compiler logs, checker snapshots,
resolved import hashes and dependency pins match the successful receipts.
No failed compiler attempt occurred for these two checks.

The stable receipts are `data/independent-parity-dependency-audit.json` and
`data/independent-odd-pair-audit.json`. The combined record is
`data/odd-pair-verification.json`.

## Scope

Even length and even start are necessary for equality; the result does not
assert their sufficiency. The strengthened pair inequality applies to the
specified actual windows. Its use in a global bound still requires the
corresponding counting or graph argument, with the window indices matched
correctly. No new numerical upper bound for the longest snake is claimed.

## Fixed evidence hashes

| Evidence | SHA256 |
|---|---|
HASH_ROWS

Combined verification SHA256: `VERIFICATION_HASH`.
'''
note=note.replace('ODD_SECONDS',f"{rows[1]['seconds']:.3f}").replace('DEP_SECONDS',f"{rows[0]['seconds']:.3f}")
hashrows=[]
for row in rows:
 for label,key in [('source','source_sha256'),('object','object_sha256'),('receipt','receipt_sha256')]:
  hashrows.append('| '+row['module']+' '+label+' | `'+row[key]+'` |')
note=note.replace('HASH_ROWS','\n'.join(hashrows)).replace('VERIFICATION_HASH',sha(vf))
nf=H/'audit/odd-pair-derivation.md';assert not nf.exists();nf.write_text(note,encoding='utf-8',newline='\n')
print(json.dumps(dict(status=out['status'],verification_sha256=sha(vf),report_sha256=sha(nf),reports=rows),indent=2))
