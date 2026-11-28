"""Count all two-ended completions, with independent reverse-order enumeration."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
from prefix import BANK, BASE, HERE, check, compile_worker


def shape(path):
    word = bytes((a ^ b).bit_length() - 1 for a, b in zip(path, path[1:]))
    def normal(w):
        axes = bytes(dict.fromkeys(w))
        return w.translate(bytes.maketrans(axes, bytes(range(len(axes)))))
    return min(normal(word), normal(word[::-1]))


class Spectrum:
    def __init__(self, scratch):
        self.scratch = scratch
        self.count = compile_worker(BASE / 'Ends.cs', scratch)
        self.replay = compile_worker(BASE / 'Replay.cs', scratch)
        self.bank = {shape(r['vertex_sequence']): i for i, r in enumerate(json.loads(BANK.read_bytes()))}

    def query(self, core, budget, capture=191):
        check(core)
        inp = self.scratch / 'input.tsv'
        output = self.scratch / 'count.tsv'
        audit = self.scratch / 'replay.tsv'
        inp.write_text('core\t%d\t%s\t%d\n' % (core[0], ','.join(map(str,core[1:-1])), core[-1]))
        subprocess.run([str(self.count), str(inp), str(output), str(budget), str(capture), 'full'], check=True)
        subprocess.run([str(self.replay), str(inp), str(audit), str(budget), 'full'], check=True)
        _, replay_closed, replay_nodes, replay_hist = audit.read_text().strip().split('\t')
        paths = {}
        with output.open() as stream:
            for line in stream:
                fields = line.rstrip().split('\t')
                if fields[0] == 'P':
                    p = list(map(int, fields[2].split(',')))
                    check(p)
                    assert any(p[j:j+len(core)] == core for j in range(len(p)-len(core)+1))
                    key = shape(p)
                    paths.setdefault(key, dict(path=p, bank=self.bank.get(key)))
                else:
                    _, _, count_closed, count_nodes, high, best, saved, first_hist = fields
        p = list(map(int, best.split(',')))
        check(p)
        assert len(p) == int(high)+1
        assert any(p[j:j+len(core)] == core for j in range(len(p)-len(core)+1))
        closed = count_closed == replay_closed == '1'
        if closed:
            assert first_hist == replay_hist
        hist = list(map(int, first_hist.split(',')))
        return dict(core=core, nodes=[int(count_nodes),int(replay_nodes)], closed=closed,
                    finished=[count_closed=='1',replay_closed=='1'], budget=budget,
                    histogram=hist, replay_histogram=list(map(int,replay_hist.split(','))),
                    maximum_seen=int(high), maximum_path=p, saved_labelled_paths=int(saved),
                    shapes={sha256(w).hexdigest(): r for w,r in paths.items()})


def main():
    donor = json.loads(BANK.read_bytes())[0]['vertex_sequence']
    blockers = {}
    for d in range(9):
        v = donor[0] ^ (1 << d)
        blockers[d] = next(i for i,w in enumerate(donor[1:],1) if (w^v).bit_count() <= 1)
    results = dict(archive='191-0', first_blocking_index=blockers,
                   source_sha256={f:sha256((BASE/f).read_bytes()).hexdigest() for f in ('Ends.cs','Replay.cs')},
                   rows={})
    output = HERE/'spectrum.json'
    if output.exists():
        earlier = json.loads(output.read_bytes())
        assert earlier['source_sha256'] == results['source_sha256']
        results['rows'] = earlier['rows']
    with TemporaryDirectory() as scratch:
        solver = Spectrum(Path(scratch))
        for length in (153,152,146,140,134,128,127,125,122,118,114,110):
            if results['rows'].get(str(length), {}).get('closed'):
                continue
            row = solver.query(donor[:length+1], 32000000)
            results['rows'][str(length)] = row
            print(length, row['closed'], row['maximum_seen'], row['nodes'], row['histogram'][-1], flush=True)
            output.write_text(json.dumps(results,separators=(',',':'))+'\n')
            if not row['closed'] or row['maximum_seen'] >= 192:
                break


if __name__ == '__main__':
    main()
