"""Keep only LRAT additions used by the final contradiction and replay before replacement."""
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import subprocess
from interval import HERE, encode, rebuild


def compact(core, row, folder, scratch, verifier, trimmer):
    if row['status']!='excluded' or 'before_trim_bytes' in row:
        return
    cnf,_=encode(core,row['target'],row['majority'],row['cycles'],row['required'],row['forbidden'])
    formula=scratch/'replay.cnf'
    assert cnf.save(formula)==row['cnf_sha256']
    archived=folder/'proofs'/row['proof']
    spool=scratch/'hints.bin'
    raw=scratch/'cone.lrat'
    candidate=archived.with_suffix('.compact.gz')
    subprocess.run([str(trimmer),str(row['clauses']),str(archived),str(spool),str(raw)],
                   check=True,capture_output=True,timeout=110)
    spool.unlink()
    h=rebuild.masks.p.joins.archive(raw,candidate)
    raw.unlink()
    row['before_trim_bytes']=archived.stat().st_size
    if candidate.stat().st_size < archived.stat().st_size:
        receipt=rebuild.masks.p.check_proof(formula,candidate,verifier)
        candidate.replace(archived)
        row.update(raw_sha256=h,replay=receipt)
    else:
        candidate.unlink()
    row['bytes']=archived.stat().st_size


def main():
    with TemporaryDirectory() as tmp:
        scratch=Path(tmp)
        verifier,trimmer=rebuild.masks.compilers(scratch)
        for filename in ('decisions.json','forced-step.json'):
            dest=HERE/filename
            data=json.loads(dest.read_bytes())
            groups=([ (r['core'],r['cases']) for r in data.values() ] if filename=='decisions.json'
                    else [(data['core'],rows) for rows in data['cases'].values()])
            for core,rows in groups:
                for row in rows.values():
                    compact(core,row,HERE,scratch,verifier,trimmer)
                    dest.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('Saved replayed contradiction cones.')


if __name__=='__main__':
    main()
