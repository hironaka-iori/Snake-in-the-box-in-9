"""Replay the selected smaller RUP proof against original full-formula identifiers."""
from pathlib import Path
import hashlib,json,time
HERE=Path(__file__).resolve().parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=HERE/'data/refine-core0.json';record=read(source)
assert record['status']=='UNSAT_TRIMMED_NOT_REPLAYED'
original=HERE/'data/012034-middle5-outer15-certificate.json';meta=read(original)
fullpath=HERE/'work/012034-middle5-outer15/full.cnf';corepath=HERE/record['cnf'];proof=HERE/record['trim']
assert sha(fullpath)==meta['cnf_sha256']==record['full_cnf_sha256']
assert sha(corepath)==record['cnf_sha256'] and sha(proof)==record['trim_sha256']
parse=lambda p:[[int(x) for x in line.split()[:-1]] for line in p.read_text().splitlines() if line and not line.startswith(('c','p'))]
full=parse(fullpath);core=parse(corepath);ids=record['input_ids']
assert len(ids)==len(core)==len(set(ids)) and core==[full[i-1] for i in ids]
def mapped(i):return ids[i-1] if i<=len(core) else len(full)+i-len(core)
database={i:full[i-1] for i in record['used_original_ids']}
active={abs(v) for row in database.values() for v in row}
last=len(full);steps=hints=0;start=time.monotonic()
with proof.open() as stream:
    for line in stream:
        row=list(map(int,line.split()));zero=row.index(0,1)
        cid=mapped(row[0]);clause=row[1:zero];antecedents=list(map(mapped,row[zero+1:-1]))
        assert row[-1]==0 and cid>last and all(0<h<cid for h in antecedents)
        assigned={-v for v in clause};conflict=any(-v in assigned for v in assigned)
        for h in antecedents:
            premise=database[h]
            if conflict or any(v in assigned for v in premise):continue
            rest={v for v in premise if -v not in assigned}
            assert len(rest)<=1
            if not rest:conflict=True
            else:assigned.add(next(iter(rest)))
        assert conflict
        database[cid]=clause;active.update(abs(v) for v in clause);last=cid
        steps+=1;hints+=len(antecedents)
assert database[last]==[] and steps==record['lemmas'] and hints==record['hints']
out=dict(status='PASS_REFINED_RUP_IN_ORIGINAL_FORMULA',refinement_sha256=sha(source),original_certificate_sha256=sha(original),
    full_cnf_sha256=sha(fullpath),core_cnf_sha256=sha(corepath),lrat_sha256=sha(proof),input_clauses=len(core),
    used_input_clauses=len(record['used_original_ids']),deductions=steps,hints=hints,active_variables=sorted(active),
    seconds=time.monotonic()-start,script_sha256=sha(Path(__file__)),
    scope='Independent native unit-propagation replay after exact input-clause mapping. Concrete counter semantics, Lean contradiction and actual-snake theorem remain pending.')
target=HERE/'data/replay-core0.json';assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'],steps,'deductions',hints,'hints',len(active),'active variables',round(out['seconds'],3),'seconds')
