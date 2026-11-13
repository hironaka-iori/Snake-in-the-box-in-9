#!/usr/bin/env python3
"""Generate replay sources ahead of `prod233.py`, so its generation phase (cadical 8 seeds x 5 rounds
per big core, serial) overlaps the kernel builds of the previous batch.

Each worker (`--worker i`) has its own scratch directory ($CERT233_SCR/pregen<i>, set before
`cert233` is imported) and its own output tree; it takes, in `work_items` order, the first unbuilt
certificate that has no source in `work/final_lean` yet, is not in the batch prod is generating or
building now (read from the command lines of its `cert233.py replay` / `guarded_lake_build.py`
children), and is not claimed by another worker (an O_EXCL file in $CERT233_SCR/pregen_claims).
It runs `cert233.py replay --out <own tree> NAME` and then moves the source into
`work/final_lean/LocalWindowUnsat` unless a source or `.olean` appeared there meanwhile (prod
generated it itself: the copy is dropped).  It also helps prod's current replay from the end of its
list backwards (prod goes forwards and skips names whose source exists).  Touch
$CERT233_SCR/pregen_stop<i> to make worker i exit before its next item (used by supervisor233.py).  The generated source is the same as prod's own
(`cert233.py replay` is deterministic given the key), so prod builds it unchanged.  Only the
--ahead first eligible certificates are taken; it stops below --min-disk-mb.

  CERT233_SCR=/home/user/cert233work setsid nohup nice -n 12 python3 pregen233.py --worker 0 &
"""
import argparse, json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
LEAN = os.path.join(ROOT, 'work', 'final_lean')
BASE = os.environ.get('CERT233_SCR', '/home/user/cert233work')


def _names(line):
    for w in line.split():
        if w.startswith('LocalWindowUnsat.'):
            w = w.split('.', 1)[1]
        if w[:1] in 'ST' and 'A' in w and '/' not in w and '-' not in w:
            yield w


def prod_current():
    """(names of prod's current replay generation, in its order; names of its guarded build)."""
    out = subprocess.run(['ps', '-eo', 'args'], capture_output=True, text=True).stdout
    rep, build = [], set()
    for line in out.splitlines():
        if 'pregen' in line:
            continue
        if 'cert233.py replay' in line:
            rep += [w for w in _names(line) if w not in rep]
        elif 'guarded_lake_build.py' in line:
            build.update(_names(line))
    return rep, build


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--worker', type=int, required=True)
    ap.add_argument('--ahead', type=int, default=30)
    ap.add_argument('--min-disk-mb', type=int, default=3000)
    ap.add_argument('--seed-jobs', default='1', help="passed to cert233.py replay ('auto': use idle cores)")
    a = ap.parse_args()
    scr = os.path.join(BASE, 'pregen%d' % a.worker)
    os.makedirs(scr, exist_ok=True)
    os.environ['CERT233_SCR'] = scr
    sys.path.insert(0, HERE)
    import cert233 as C
    claims = os.path.join(BASE, 'pregen_claims')
    os.makedirs(claims, exist_ok=True)
    out = os.path.join(scr, 'out')
    stop = os.path.join(BASE, 'pregen_stop%d' % a.worker)   # touch to stop after the current item
    ns = C.argparse.Namespace(keys_from='', plan=C.PLAN, core=C.CORE, names=[])
    olean = lambda n: os.path.exists(os.path.join(LEAN, '.lake/build/lib/lean/LocalWindowUnsat', n + '.olean'))  # noqa
    src = lambda n: os.path.join(LEAN, 'LocalWindowUnsat', n + '.lean')  # noqa
    log = lambda r: print(json.dumps({'t': round(time.time()), **r}), flush=True)  # noqa
    while True:
        if C.disk_free_mb() < a.min_disk_mb:
            log({'stop': 'disk', 'free_mb': C.disk_free_mb()})
            return
        items = [it[2] for h, it, m in C.work_items(ns, {'seed', 'share'}) if not olean(it[2])]
        if not items:
            log({'done': 'all built'})
            return
        if os.path.exists(stop):
            os.remove(stop)
            log({'stop': 'requested'})
            return
        rep, build = prod_current()
        # prod's own replay goes through its list in order and skips names whose source exists:
        # help it from the end of its list backwards, then take the items after its batch.
        mine = [n for n in reversed(rep) if not os.path.exists(src(n)) and not olean(n)]
        todo = mine + [n for n in items if n not in rep and n not in build and not os.path.exists(src(n))][:a.ahead]
        pick = None
        for n in todo:
            try:
                os.close(os.open(os.path.join(claims, n), os.O_CREAT | os.O_EXCL | os.O_WRONLY))
                pick = n
                break
            except FileExistsError:
                continue
        if pick is None:
            time.sleep(60)
            continue
        t0 = time.time()
        r = subprocess.run([sys.executable, os.path.join(HERE, 'cert233.py'), 'replay', '--kinds', 'seed,share',
                            '--min-disk-mb', str(a.min_disk_mb), '--seed-jobs', a.seed_jobs, '--out', out, pick],
                           capture_output=True, text=True, env=dict(os.environ, CERT233_SCR=scr))
        p = os.path.join(out, 'LocalWindowUnsat', pick + '.lean')
        if r.returncode != 0 or not os.path.exists(p):
            log({'name': pick, 'failed': r.returncode, 'stderr': r.stderr[-800:]})
            if os.path.exists(p):
                os.remove(p)
            continue   # the claim stays: prod generates this one itself
        if os.path.exists(src(pick)) or olean(pick):
            # prod generated it meanwhile (the same deterministic text): drop the copy.  A source prod is
            # still writing is overwritten by identical text; prod builds only after its replay ends.
            os.remove(p)
            log({'name': pick, 'dropped': 'prod got there first', 's': round(time.time() - t0)})
        else:
            os.replace(p, src(pick))
            log({'name': pick, 'moved': True, 's': round(time.time() - t0)})


if __name__ == '__main__':
    main()
