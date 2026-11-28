"""Decide target 192 on the named prefix and release its last edge on exclusion."""
import json
import subprocess
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / '278-regrowing-two-free-ends'
BANK = HERE.parents[1] / 'work/bank9.json'
CSC = 'C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe'


def check(path):
    assert len(set(path)) == len(path) and all(0 <= x < 512 for x in path)
    for j, v in enumerate(path):
        for i in range(j):
            assert ((path[i] ^ v).bit_count() == 1) == (i + 1 == j)


def compile_worker(source, scratch):
    exe = scratch / (source.stem + '.exe')
    subprocess.run([CSC, '/nologo', '/optimize+', '/platform:x64', '/out:' + str(exe),
                    str(source)], check=True)
    return exe


def prefix():
    donor = json.loads(BANK.read_bytes())[0]['vertex_sequence']
    check(donor)
    assert len(donor) == 192
    source = BASE / 'TwoTailIndexed.cs'
    results = dict(archive='191-0', donor=donor, worker_sha256=sha256(source.read_bytes()).hexdigest(),
                   arguments=[192, 12000000, 150000, 50000000, 75000], prefixes={})
    with TemporaryDirectory() as folder:
        exe = compile_worker(source, Path(folder))
        for n in (153, 152):
            core = donor[:n + 1]
            job = subprocess.run([str(exe), *map(str, results['arguments'])],
                                 input='prefix\t' + ','.join(map(str, core)) + '\n',
                                 text=True, capture_output=True, check=True)
            key, outcome, a, b, ea, eb, mn, cn, ls, rs, pairs, why, lh, rh, witness, iw, tw = job.stdout.strip().split('\t')
            row = dict(status=outcome, reason=why, left_max=int(a), right_max=int(b),
                       left_exact=int(ea), right_exact=int(eb), mask_nodes=int(mn),
                       contact_nodes=int(cn), left_stored=int(ls), right_stored=int(rs),
                       pairs=int(pairs), index_work=int(iw), trie_work=int(tw),
                       left_histogram=lh, right_histogram=rh)
            if outcome == 'WITNESS':
                path = list(map(int, witness.split(',')))
                check(path)
                assert len(path) == 193 and any(path[i:i+n+1] == core for i in range(len(path)-n))
                row['path'] = path
            results['prefixes'][n] = row
            (HERE / 'prefix.json').write_text(json.dumps(results, indent=2) + '\n')
            print(n, outcome, why, a, b, mn, pairs, flush=True)
            if outcome != 'EXCLUDED':
                break


if __name__ == '__main__':
    prefix()
