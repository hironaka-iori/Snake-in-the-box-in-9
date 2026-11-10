"""Rebuild, on this branch, the Lean proofs of the five share floors that `Floors233` assumes.

The floors are theorems of origin/main (`Snake9.ShareTransfer152.share16`,
`Snake9.CriticalShare155.share17` and the three `LocalWindow.ShareWindow73xx.refuted`
certificates behind `Snake9.CatalogueIntegration73.canonical7300/7304/7306`).  Their import
closure is listed in `milestones/33-233-lean/data/main_floor_modules.json`, in topological
order: 1061 modules, 19 of which are byte-identical to modules of this branch (`source:
"branch"`; this branch's `Snake9` and `DirectionWindowBridge` are supersets of main's
`lean-core` copies, see FLOORS.md) and reuse this branch's `.olean` files.

Every other module is fetched from main at the pinned commit through the GitHub API (by git
blob sha; the replay sources of milestone 151 and the case sources of milestone 73 come from
the archives committed on main, also by blob sha) and checked against its recorded git blob
sha before it is compiled.  Each module is compiled by one `lean -o` (never lake), `nice -n
10`, with `LEAN_PATH` = build dir, this branch's core and chain build dirs, then mathlib
(pinned c44e0c8e, the same mathlib as main's records), and a watchdog that kills the
compiler (by its PID) above `--max-rss-gb`.  `--delete-sources` removes each source once its
`.olean` exists, so the peak disk use is the `.olean` files plus one source.

    python3 milestones/33-233-lean/scripts/port_main_floors.py --build-dir B [--only M ...]
        [--until M] [--max-rss-gb 3] [--delete-sources] [--log L]

The run is resumable: a module whose `.olean` is already in the build dir is skipped.
"""
import argparse, hashlib, io, json, os, subprocess, sys, tarfile, threading, time, zipfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
MANIFEST = REPO / 'milestones/33-233-lean/data/main_floor_modules.json'
CORE = REPO / 'work/final_lean/.lake/build/lib/lean'
CHAIN = REPO / 'work/spectral/.verification/chain'
MATHLIB = Path(os.environ.get('SNAKE9_MATHLIB') or next(
    (q for q in (Path.home() / 'lean-deps/mathlib4', Path('/home/user/lean-deps/mathlib4')) if q.exists()),
    Path.home() / 'lean-deps/mathlib4'))
LEAN = Path.home() / '.elan/toolchains/leanprover--lean4---v4.19.0/bin/lean'


def git_blob_sha(data: bytes) -> str:
    return hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest()


def gh_blob(repo: str, sha: str) -> bytes:
    r = subprocess.run(['gh', 'api', '-H', 'Accept: application/vnd.github.raw',
                        f'repos/{repo}/git/blobs/{sha}'], capture_output=True, check=True)
    return r.stdout


class Sources:
    def __init__(self, man, cache: Path):
        self.man, self.cache, self.arch = man, cache, {}

    def get(self, m: str) -> bytes:
        e = self.man['modules'][m]
        s = e['source']
        if 'blob' in s:
            data = gh_blob(self.man['repo'], s['blob'])
        else:
            key = s['archive_blob']
            if key not in self.arch:
                f = self.cache / (key + ('.zip' if s['archive'].endswith('.zip') else '.tgz'))
                if not f.exists():
                    f.write_bytes(gh_blob(self.man['repo'], key))
                self.arch[key] = (zipfile.ZipFile(f) if f.suffix == '.zip' else tarfile.open(f))
            a = self.arch[key]
            data = a.read(s['member']) if isinstance(a, zipfile.ZipFile) else a.extractfile(s['member']).read()
        # Main's committed blobs may carry CRLF; the recorded sha is of the LF form when it came
        # from an archive.  Accept either form.
        if e['git_blob'] not in (git_blob_sha(data), git_blob_sha(data.replace(b'\r\n', b'\n'))):
            raise SystemExit(f'{m}: source does not match the recorded git blob {e["git_blob"]}')
        return data


def rss_gb(pid: int) -> float:
    try:
        for line in open(f'/proc/{pid}/status'):
            if line.startswith('VmRSS:'):
                return int(line.split()[1]) / 2**20
    except OSError:
        pass
    return 0.0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--build-dir', required=True, type=Path)
    ap.add_argument('--only', nargs='*', help='build these modules and their missing imports only')
    ap.add_argument('--until', help='stop after this module (in manifest order)')
    ap.add_argument('--max-rss-gb', type=float, default=3.0)
    ap.add_argument('--delete-sources', action='store_true')
    ap.add_argument('--log', type=Path)
    a = ap.parse_args()
    man = json.loads(MANIFEST.read_text())
    mods = man['modules']
    build = a.build_dir.resolve()
    (build / '_archives').mkdir(parents=True, exist_ok=True)
    src = Sources(man, build / '_archives')
    log = open(a.log, 'a') if a.log else None

    def out(s):
        print(s, flush=True)
        if log:
            log.write(s + '\n'); log.flush()

    mpaths = [MATHLIB / '.lake/build/lib/lean'] + sorted(
        p / '.lake/build/lib/lean' for p in (MATHLIB / '.lake/packages').iterdir())
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [build, CORE, CHAIN, *mpaths])))

    def olean(m):
        return Path(*m.split('.')).with_suffix('.olean')

    def have(m):
        return any((d / olean(m)).exists() for d in (build, CORE, CHAIN))

    order = man['order']
    if a.only:
        need, st = set(), list(a.only)
        while st:
            m = st.pop()
            if m in need or m not in mods or have(m):
                continue
            need.add(m); st += mods[m]['imports']
        order = [m for m in order if m in need]
    total = 0.0
    for m in order:
        if have(m):
            continue
        e = mods[m]
        if e['source'] == 'branch':
            hits = list(REPO.glob('work/**/' + str(Path(*m.split('.')).with_suffix('.lean'))))
            hits = [h for h in hits if '.lake' not in h.parts and '.verification' not in h.parts
                    and git_blob_sha(h.read_bytes()) == e['git_blob']]
            if not hits:
                raise SystemExit(f'{m}: no identical branch source and no built .olean')
            data = hits[0].read_bytes()
        else:
            data = src.get(m)
        f = build / Path(*m.split('.')).with_suffix('.lean')
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_bytes(data)
        o = build / olean(m)
        t = time.time()
        p = subprocess.Popen(['nice', '-n', '10', str(LEAN), f'--root={build}', '-o', str(o), str(f)],
                             env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        peak, killed = [0.0], [False]

        def watch():
            while p.poll() is None:
                # nice execs lean in place, so p.pid is the compiler's PID
                r = rss_gb(p.pid); peak[0] = max(peak[0], r)
                if r > a.max_rss_gb:
                    killed[0] = True; p.kill(); return
                time.sleep(0.5)
        w = threading.Thread(target=watch); w.start()
        stdout, _ = p.communicate(); w.join()
        dt = time.time() - t; total += dt
        bad = p.returncode != 0 or "declaration uses 'sorry'" in stdout or killed[0]
        axioms = [l for l in stdout.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l]
        nonstd = [l for l in axioms if any(x not in ('propext', 'Classical.choice', 'Quot.sound')
                  for x in l.split('[')[-1].rstrip(']').replace(' ', '').split(',') if '[' in l and x)]
        out(f'{m}: {"FAILED" if bad else "ok"} {dt:.1f}s rss {peak[0]:.2f} GB '
            f'src {len(data)//1024} kB olean {o.stat().st_size//1024 if o.exists() else 0} kB '
            f'axiom reports {len(axioms)}{" NONSTANDARD " + str(nonstd) if nonstd else ""}')
        if bad:
            out(stdout[-4000:])
            if o.exists():
                o.unlink()
            sys.exit(1)
        if nonstd:
            sys.exit(2)
        if a.delete_sources:
            f.unlink()
        if a.until and m == a.until:
            break
    out(f'# done, {total:.0f}s compile wall time')


if __name__ == '__main__':
    main()
