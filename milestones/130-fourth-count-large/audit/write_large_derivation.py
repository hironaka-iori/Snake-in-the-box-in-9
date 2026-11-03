"""Audit successful semantic receipts and write their exact mathematical scope."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
rows=[];pins={}
for module,kind in [('LargeLower130','lower'),('LargeClauses130','clauses')]:
 rp=H/'data'/f'independent-large-{kind}-audit.json';q=read(rp)
 assert q['status']=='PASS' and q['exit_code']==0 and not q.get('timeout',False) and q['dependencies_unchanged']
 for name,digest in q['dependencies'].items():assert sha(Path(name))==digest,name
 source=H/'lean'/(module+'.lean');checker=H/'audit'/f'check_large_{kind}.py';log=Path(q['log'])
 assert sha(source)==q['source_sha256']==q['source_current_sha256']==sha(log.parent/'source.lean.txt')
 assert sha(checker)==q['checker_sha256']==q['checker_current_sha256']==sha(log.parent/'checker.py.txt')
 for key in ['object','importable_object','log']:assert sha(Path(q[key]))==q[key+'_sha256']
 assert len(q['axioms'])==5 and all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in q['axioms'])
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.read_text())
 for p in [rp,source,checker,log,Path(q['object']),Path(q['importable_object']),log.parent/'record.json',log.parent/'source.lean.txt',log.parent/'checker.py.txt']:
  pins[p.relative_to(H).as_posix()]=sha(p)
 rows.append(dict(module=module,receipt=rp.relative_to(H).as_posix(),receipt_sha256=sha(rp),
                  source_sha256=sha(source),object_sha256=q['importable_object_sha256'],
                  seconds=q['seconds'],axioms=q['axioms']))
data=read(H/'data/lean-data-review.json')
assert data['status']=='PASS_EXACT_LEAN_LARGE_DATA_AND_CNF_TAIL'
assert (data['clauses'],data['tags'],data['registers'],data['occurrences'],data['distinct_vertices'])==(717,717,357,21,21)
for name,digest in data['pins'].items():assert sha(H/name)==digest; pins[name]=digest
for name in ['data/preparation.json','data/lean-data-review.json','audit/generate_large_clauses.py',
             'audit/concrete-large-generation.json','audit/prepare_checkers.py','audit/checker-generation.json',
             'audit/write_large_derivation.py']:
 pins[name]=sha(H/name)
out=dict(status='PASS_ACTUAL_LARGE_COUNTER_717_CLAUSES',lean_modules=2,axiom_reports=10,
 actual_selected_cap=17,fourth_count_lower=4,clauses=717,registers=357,
 actual_canonical_window_satisfaction=True,full_105246_clause_satisfaction=False,
 complete_refutation=False,new_six_count_floor=False,new_global_upper_bound=False,
 reports=rows,pins=pins,
 scope='For a fitting canonical0120324 window and actual fourth count>=4, an actual normalized assignment satisfies exactly the717 added clauses. No six-total cap or pair-count hypothesis is required.')
vf=H/'data/large-semantics-verification.json';assert not vf.exists()
vf.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
note=r'''# The fourth-count constraint and its concrete clauses

Both semantic modules passed Lean. For an actual snake and a fitting window
whose canonical direction sequence is \(0120324\), the hypothesis
\(\alpha_{r+4}\ge4\) implies that at most seventeen of the fourth centre's
twenty-one opposite corners are selected. The concrete result supplies a
coordinate permutation and proves satisfaction of exactly the 717 added
counter clauses.

The hypotheses are the actual snake, the fitting window, its canonical word,
and the fourth-count lower bound. The proof requires no six-count total cap,
pair-count inequality, or equality-case lower bounds for the first and second
counts.

## Count conversion

In canonical coordinates the window vertices are

\[
0,1,3,7,6,14,10,26.
\]

The fourth centre is vertex 6, with incident path directions 0 and 3. Its
twenty-one opposite corners arise by choosing two of the seven unused
directions. Lean checks the explicit corner list against that construction.
The selected and absent counts add to twenty-one. The established frame
identity identifies the absent count with \(\alpha_{r+4}\), giving

\[
\#\{\text{selected opposite corners at the fourth centre}\}
+\alpha_{r+4}=21.
\]

Consequently \(\alpha_{r+4}\ge4\) gives the selected-corner cap seventeen.
The normalization theorem constructs the required coordinate permutation
from the canonical direction-word hypothesis.

## Concrete added clauses

The semantic certificate retains counter index 9, the twenty-one primary
inputs and all 357 fresh registers numbered 8706 through 9062. The nine
preceding counter entries are empty defaults because their clauses are
outside this certificate. All 512 primary meanings remain present. No older
auxiliary register occurs in the checked 717-clause list.

Lean checks every literal meaning and all clause tags. The clause checks are
split into twelve groups of at most 64 clauses, then assembled into the exact
raw clause list. Counter-tag validity is independent of the window argument.
The count conversion supplies the counter bound; the existing clause
soundness theorem supplies satisfaction under the actual normalized
assignment. The final theorem constructs the normalization and concludes
satisfaction of the added clauses directly from the stated actual-window
hypotheses.

A separate parser checks the saved Lean raw lists, tags, counter literals and
every meaning index from 0 through 9062 against the counter metadata and the
last 717 clauses of the saved search input. This verifies the data connection;
the mathematical interpretation is supplied by the successful Lean checks.

## Successful checks

| Module | Public reports | Elapsed seconds |
|---|---:|---:|
| `LargeLower130` | 5 | LOWER_SECONDS |
| `LargeClauses130` | 5 | CLAUSE_SECONDS |

All ten reports contain only subsets of `propext`, `Classical.choice` and
`Quot.sound`. The concrete literal check has no axioms. Source bytes,
compiler logs, object bytes, dependency pins and checker snapshots were
verified against the successful receipts. Both checks passed their fresh
resource gates before launch. No failed Lean attempt occurred in this task.

The stable receipts are `data/independent-large-lower-audit.json` and
`data/independent-large-clauses-audit.json`. The combined verification is
`data/large-semantics-verification.json`; the exact Lean-data comparison is
`data/lean-data-review.json`. The interrupted earlier draft of
`LargeLower130.lean` was preserved without modification. Historical generator
records retain their original generated-but-not-yet-checked status; these
successful receipts provide the later checked status.

## Scope

This result justifies the 717 clauses appended to the existing 104529-clause
input. Satisfaction of the complete 105246-clause conjunction and any
contradiction of it remain separate proof obligations. Neither a new
six-count lower bound nor a new global upper bound follows from this semantic
result alone.

## Fixed source and receipt hashes

| Evidence | SHA256 |
|---|---|
HASH_ROWS

The combined verification record's SHA256 is `VERIFICATION_HASH`.
'''
note=note.replace('LOWER_SECONDS',f"{rows[0]['seconds']:.3f}").replace('CLAUSE_SECONDS',f"{rows[1]['seconds']:.3f}")
hashrows=[]
for x in rows:
 for label,key in [('source','source_sha256'),('object','object_sha256'),('receipt','receipt_sha256')]:
  hashrows.append('| '+x['module']+' '+label+' | `'+x[key]+'` |')
note=note.replace('HASH_ROWS','\n'.join(hashrows)).replace('VERIFICATION_HASH',sha(vf))
nf=H/'audit/large-derivation.md';assert not nf.exists();nf.write_text(note,encoding='utf-8',newline='\n')
print(json.dumps(dict(status=out['status'],verification_sha256=sha(vf),report_sha256=sha(nf),reports=rows),indent=2))
