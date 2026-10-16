import gzip
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = ROOT / 'outputs/keep96'
sys.path.insert(0, str(HERE / '.packages'))
sys.path.insert(0, str(ROOT / 'work'))
from build_regrowth_cnf import encode, witness_assignment


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def save(p, data):
    p = Path(p)
    p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_suffix(p.suffix + '.tmp')
    tmp.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')
    tmp.replace(p)


def compressed(p, text):
    Path(p).write_bytes(gzip.compress(text.encode(), mtime=0))


def bank():
    paths = [r['vertex_sequence'] for r in json.loads((ROOT / 'work/bank9.json').read_text())]
    if len(paths) != 131:
        raise ValueError('expected 131 paths')
    return [p for s in paths for p in (s, s[::-1])]


def verify_path(path):
    if not path or any(type(v) is not int or not 0 <= v < 512 for v in path):
        raise ValueError('invalid vertices')
    for i, v in enumerate(path):
        for j in range(i + 1, len(path)):
            d = (v ^ path[j]).bit_count()
            if d == 0 or ((d == 1) != (j == i + 1)):
                raise ValueError(f'not induced: {i},{j}')


def formula(entry):
    data = encode(bank()[entry], keep=96, total_vertices=193)
    directory = OUT / 'formulas'
    directory.mkdir(parents=True, exist_ok=True)
    stem = directory / f'entry{entry:03d}'
    cnf = f"p cnf {data['variables']} {len(data['clauses'])}\n" + ''.join(
        ' '.join(map(str, c)) + ' 0\n' for c in data['clauses'])
    meta = json.dumps(data, separators=(',', ':')) + '\n'
    paths = [stem.with_suffix('.cnf.gz'), stem.with_suffix('.json.gz')]
    for p, text in zip(paths, (cnf, meta)):
        encoded = gzip.compress(text.encode(), mtime=0)
        if p.exists() and p.read_bytes() != encoded:
            raise ValueError('existing formula differs; use a new isolated run directory')
        if not p.exists():
            p.write_bytes(encoded)
    return data, {p.relative_to(ROOT).as_posix(): sha(p) for p in paths}
