"""Small soundness controls, including rejection of corrupt and RAT proofs."""
from pathlib import Path
import tempfile
from replay import check

with tempfile.TemporaryDirectory() as d:
    p=Path(d);c=p/'f.cnf';r=p/'f.lrat'
    c.write_text('p cnf 1 2\n1 0\n-1 0\n');r.write_text('3 0 1 2 0\n')
    assert check(c,r)['additions']==1
    for bad in ['3 0 1 0\n','3 0 1 -2 0\n','3 0 2 2 0\n']:
        r.write_text(bad)
        try:check(c,r)
        except AssertionError:pass
        else:raise AssertionError('Corrupted or unsupported proof accepted')
    c.write_text('p cnf 2 3\n1 2 0\n-1 0\n-2 0\n');r.write_text('4 0 2 3 1 0\n')
    assert check(c,r)['additions']==1
print('PASS: 2 valid proofs accepted; 3 corrupted/unsupported proofs rejected')
