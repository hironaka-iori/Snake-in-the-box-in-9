"""Parallel driver for work/snake_dfs.c (experimental search, not certificates).

Build first:  cc -O3 -march=native -o work/snake_dfs work/snake_dfs.c

  python work/dfs_driver.py regrow --keep 120 --target 193 --nodes 4000000000
  python work/dfs_driver.py partner --seed outputs/snake8_witness.json --target 97
  python work/dfs_driver.py plateau --window 24 --rounds 4 --keep 120
  python work/dfs_driver.py combo --jobs 2000 --seconds 1800

Every reported path is re-verified here by check_snake.verify before it is saved.
"""
import argparse, json, os, random, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = os.environ.get('SNAKE_DFS', str(ROOT / 'work' / 'snake_dfs'))
sys.path.insert(0, str(ROOT / 'work'))
from check_snake import verify  # noqa: E402


def run(args, snakes):
    text = ''.join(f"{len(s)} {' '.join(map(str, s))}\n" for s in snakes)
    out = subprocess.run([BIN] + [str(a) for a in args], input=text, capture_output=True,
                         text=True, check=True).stdout
    return [json.loads(line) for line in out.splitlines() if line.strip()]


def checked(vertices, n=9):
    """Translate to start at 0 and run the independent all-pairs check."""
    shift = vertices[0]
    vs = [v ^ shift for v in vertices]
    t = [(u ^ v).bit_length() - 1 for u, v in zip(vs, vs[1:])]
    r = verify(t, n)
    assert r['vertex_sequence'] == vs
    return r


def save_record(path_vertices, note, n=9):
    r = checked(path_vertices, n)
    out = ROOT / 'outputs' / f"dfs_record_{r['edges']}_{int(time.time())}.json"
    r['note'] = note
    out.write_text(json.dumps(r, indent=2), encoding='utf-8')
    print(f"*** RECORD {r['edges']} edges saved to {out}", flush=True)


def bank():
    return [e['vertex_sequence'] for e in json.loads((ROOT / 'work' / 'bank9.json').read_text())]


def cmd_regrow(a):
    snakes = bank() if not a.input else [json.loads(l)['path'] for l in Path(a.input).read_text().splitlines() if l.strip()]
    out = Path(a.output or ROOT / 'outputs' / f'dfs_regrow_keep{a.keep}.json')
    # Incremental log: one line per finished (index, orientation); a rerun resumes from it.
    log = out.with_suffix('.partial.jsonl')
    done = {}
    if log.exists():
        for line in log.read_text().splitlines():
            r = json.loads(line)
            if r['node_limit'] == a.nodes and r['target'] == a.target:
                done[(r['index'], r['reversed'])] = r
    lock = __import__('threading').Lock()
    begin = time.monotonic()

    def job(task):
        i, rev = task
        if (i, rev) in done:
            return [done[(i, rev)]]
        s = snakes[i][::-1] if rev else snakes[i]
        res = run(['regrow', 9, a.keep, a.target, a.nodes, -1, 1], [s])
        rows = []
        for r in res:
            if r['event'] == 'regrow':
                r.update(index=i, reversed=rev, node_limit=a.nodes)
                rows.append(r)
            elif r['event'] == 'record':
                save_record(r['path'], f'regrow keep={a.keep} from input {i} reversed={rev}')
        with lock, log.open('a') as f:
            for r in rows:
                f.write(json.dumps(r) + '\n')
        return rows

    tasks = [(i, rev) for i in range(len(snakes)) for rev in (0, 1)]
    with ThreadPoolExecutor(a.workers) as ex:
        results = [r for rs in ex.map(job, tasks) for r in rs]
    counts = {s: sum(r['status'] == s for r in results) for s in ('FOUND', 'UNKNOWN', 'INFEASIBLE')}
    report = {'model': 'exhaustive end regrowth in Q9, prefix of KEEP vertices fixed, both orientations',
              'keep': a.keep, 'target_vertices': a.target, 'node_limit': a.nodes,
              'inputs': a.input or 'work/bank9.json', 'elapsed_seconds': round(time.monotonic() - begin, 1),
              'counts': counts, 'total_nodes': sum(r['nodes'] for r in results), 'results': results}
    out.write_text(json.dumps(report, indent=1), encoding='utf-8')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}), flush=True)


def cmd_partner(a):
    """Longest Q8 partner from an endpoint of a fixed Q8 seed (single-crossing model)."""
    seed = json.loads(Path(a.seed).read_text())['vertex_sequence']
    rows = []
    for rev in (False, True):
        s = seed[::-1] if rev else seed
        lifted = s + [s[-1] | 256]          # cross coordinate 8 at the seed's last vertex
        keep = len(lifted)
        for partner in range(a.target, a.min - 1, -1):
            target = keep + partner          # partner edges after the crossing vertex
            t0 = time.monotonic()
            r = [x for x in run(['regrow', 9, keep, target, a.nodes, 8, 1], [lifted]) if x['event'] in ('regrow', 'record')]
            st = r[0]
            row = {'joining_endpoint': s[-1], 'seed_reversed': rev, 'partner_edges': partner,
                   'joined_edges': len(s) - 1 + partner + 1, 'status': st['status'], 'nodes': st['nodes'],
                   'seconds': round(time.monotonic() - t0, 1)}
            if st['status'] == 'FOUND':
                rec = [x for x in r if x['event'] == 'record'][0]['path']
                row['joined_check_edges'] = checked(rec)['edges']
                row['partner_path'] = [v & 255 for v in rec[keep - 1:]]
            rows.append(row)
            print(json.dumps({k: v for k, v in row.items() if k != 'partner_path'}), flush=True)
            if st['status'] == 'FOUND':
                break
    out = Path(a.output or ROOT / 'outputs' / 'dfs_partner.json')
    out.write_text(json.dumps({'seed': a.seed, 'node_limit': a.nodes, 'rows': rows}, indent=1), encoding='utf-8')


def cmd_plateau(a):
    """Random walk on 191-edge snakes via equal-length internal window replacements,
    followed by exhaustive end regrowth of every new snake."""
    rng = random.Random(a.seed)
    pool = bank()
    seen = {tuple(s) for s in pool} | {tuple(s[::-1]) for s in pool}
    fresh = []
    begin = time.monotonic()
    frontier = pool[:]
    for rnd in range(a.rounds):
        def job(i):
            s = frontier[i]
            return run(['window', 9, a.window, a.tries, a.maxalt, a.wnodes, rng.randrange(1 << 30) + i], [s])
        with ThreadPoolExecutor(a.workers) as ex:
            outs = list(ex.map(job, range(len(frontier))))
        nxt = []
        for res in outs:
            for r in res:
                if r['event'] == 'record':
                    save_record(r['path'], f'window replacement, round {rnd}')
                if r['event'] == 'plateau' and r['verified']:
                    t = tuple(r['path'])
                    if t not in seen:
                        seen.add(t); seen.add(t[::-1]); nxt.append(r['path'])
        rng.shuffle(nxt)
        nxt = nxt[:a.cap]
        print(f'round {rnd}: {len(nxt)} new 191-edge snakes (cap {a.cap})', flush=True)
        fresh += nxt
        frontier = nxt or frontier
    tmp = ROOT / 'outputs' / f'dfs_plateau_pool_s{a.seed}.jsonl'
    tmp.write_text(''.join(json.dumps({'path': s}) + '\n' for s in fresh), encoding='utf-8')
    print(f'pool saved: {len(fresh)} snakes, {time.monotonic() - begin:.0f}s', flush=True)


def cmd_combo(a):
    """Random large-neighbourhood moves: truncate to CUT vertices, refill an internal
    window with any induced filling up to 2*SLACK edges shorter, then exhaustively regrow
    the end (per-filling node budget).  Each job uses one random configuration."""
    rng = random.Random(a.seed)
    snakes = []
    for s in bank():
        snakes += [s, s[::-1]]
    begin = time.monotonic()
    stats = {'jobs': 0, 'windows': 0, 'fillings': 0, 'window_unknown': 0, 'regrow_unknown': 0, 'records': 0}
    rows = []

    def job(j):
        if time.monotonic() - begin > a.seconds:
            return None
        r = random.Random(a.seed * 1000003 + j)
        i = r.randrange(len(snakes))
        cut = r.randint(a.cut_min, a.cut_max)
        w = r.randint(a.w_min, a.w_max)
        slack = r.randint(1, a.slack)
        res = run(['combo', 9, w, slack, cut, a.target, a.tries, a.wnodes, a.rnodes, r.randrange(1 << 30)], [snakes[i]])
        return i, cut, w, slack, res

    with ThreadPoolExecutor(a.workers) as ex:
        for out in ex.map(job, range(a.jobs)):
            if out is None:
                continue
            i, cut, w, slack, res = out
            stats['jobs'] += 1
            for r in res:
                if r['event'] == 'record':
                    stats['records'] += 1
                    save_record(r['path'], f'combo snake={i // 2} reversed={i % 2} cut={cut} window={r["window"]} slack={slack}')
                elif r['event'] == 'window':
                    stats['windows'] += 1
                    stats['fillings'] += r['alternatives']
                    stats['window_unknown'] += r['status'] == 'UNKNOWN'
                    stats['regrow_unknown'] += r['regrow_unknown']
                    rows.append({'bank_index': i // 2, 'reversed': i % 2, 'cut': cut, 'slack': slack, **r})
    report = {'model': 'truncate + shorter internal window refill + exhaustive end regrowth (random LNS)',
              'target_vertices': a.target, 'seed': a.seed, 'elapsed_seconds': round(time.monotonic() - begin, 1),
              'params': {k: getattr(a, k) for k in ('cut_min', 'cut_max', 'w_min', 'w_max', 'slack', 'tries', 'wnodes', 'rnodes')},
              'stats': stats, 'windows': rows}
    out = Path(a.output or ROOT / 'outputs' / f'dfs_combo_s{a.seed}.json')
    out.write_text(json.dumps(report, indent=1), encoding='utf-8')
    print(json.dumps({k: v for k, v in report.items() if k != 'windows'}), flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('regrow'); p.add_argument('--keep', type=int, default=128)
    p.add_argument('--target', type=int, default=193); p.add_argument('--nodes', type=int, default=10**10)
    p.add_argument('--input'); p.add_argument('--output'); p.add_argument('--workers', type=int, default=14)
    p = sub.add_parser('partner'); p.add_argument('--seed', default=str(ROOT / 'outputs' / 'snake8_witness.json'))
    p.add_argument('--target', type=int, default=97); p.add_argument('--min', type=int, default=80)
    p.add_argument('--nodes', type=int, default=10**10); p.add_argument('--output')
    p = sub.add_parser('plateau'); p.add_argument('--window', type=int, default=20)
    p.add_argument('--tries', type=int, default=6); p.add_argument('--maxalt', type=int, default=20)
    p.add_argument('--wnodes', type=int, default=20_000_000); p.add_argument('--rounds', type=int, default=3)
    p.add_argument('--cap', type=int, default=400); p.add_argument('--seed', type=int, default=1)
    p.add_argument('--workers', type=int, default=14)
    p = sub.add_parser('combo'); p.add_argument('--jobs', type=int, default=2000)
    p.add_argument('--seconds', type=float, default=1800); p.add_argument('--target', type=int, default=193)
    p.add_argument('--cut-min', type=int, default=140); p.add_argument('--cut-max', type=int, default=180)
    p.add_argument('--w-min', type=int, default=16); p.add_argument('--w-max', type=int, default=48)
    p.add_argument('--slack', type=int, default=2); p.add_argument('--tries', type=int, default=3)
    p.add_argument('--wnodes', type=int, default=20_000_000); p.add_argument('--rnodes', type=int, default=200_000)
    p.add_argument('--seed', type=int, default=1); p.add_argument('--workers', type=int, default=12)
    p.add_argument('--output')
    a = ap.parse_args()
    {'regrow': cmd_regrow, 'partner': cmd_partner, 'plateau': cmd_plateau, 'combo': cmd_combo}[a.cmd](a)
