import csv, json, hashlib
from pathlib import Path
from check_snake import verify

def canonical(actions):
    def normalize(xs):
        mapping = {}
        return tuple(mapping.setdefault(x, len(mapping)) for x in xs)
    return min(normalize(actions), normalize(reversed(actions)))

bank = []
with open('work/record_snakes.csv', newline='') as f:
    for row in csv.DictReader(f):
        if int(row['n']) != 9:
            continue
        actions = list(map(int, row['actions'].split()))
        result = verify(actions)
        assert result['vertex_sequence'] == list(map(int, row['vertices'].split()))
        assert result['edges'] == int(row['length']) == 191
        bank.append(result)
assert len({canonical(p['transition_sequence']) for p in bank}) == len(bank)
out = {'count':len(bank), 'all_valid': True,
       'all_unextendable':all(not p['extensions'] for p in bank),
       'all_pairs_checked':sum(p['pairs_checked'] for p in bank),
       'source':'https://github.com/Math-AI-Caltech/Snake-in-the-Box',
       'archive_sha256':hashlib.sha256(Path('work/record_snakes.csv.zip').read_bytes()).hexdigest()}
Path('outputs/snake9_bank_audit.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
Path('work/bank9.json').write_text(json.dumps(bank), encoding='utf-8')
print(json.dumps(out, indent=2))
