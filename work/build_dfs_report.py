"""Generate data fragments for paper/dfs_report/dfs_report.tex.

Runs small live demonstrations with work/snake_dfs and summarises the saved
outputs/dfs_*.json records.  Rerun after long searches finish, then rebuild:

  python work/build_dfs_report.py
  cd outputs/dfs_report && latexmk -pdf dfs_report.tex
"""
import json, os, statistics, subprocess, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = str(ROOT / 'work' / 'snake_dfs')
OUT = ROOT / 'paper' / 'dfs_report'
OUT.mkdir(exist_ok=True)
bank = [e['vertex_sequence'] for e in json.loads((ROOT / 'work' / 'bank9.json').read_text())]


def run(args, snakes, env=None):
    text = ''.join(f"{len(s)} {' '.join(map(str, s))}\n" for s in snakes)
    e = dict(os.environ, **(env or {}))
    t0 = time.monotonic()
    out = subprocess.run([BIN] + [str(a) for a in args], input=text, capture_output=True, text=True,
                         env=e, check=True).stdout
    return [json.loads(l) for l in out.splitlines() if l.strip()], time.monotonic() - t0


def trans(vs):
    return [(u ^ v).bit_length() - 1 for u, v in zip(vs, vs[1:])]


def sci(x):
    if x < 10_000:
        return f'{x:,}'.replace(',', '{,}')
    m, e = f'{x:.1e}'.split('e')
    return rf'${m}\times10^{{{int(e)}}}$'


macros, frags = [], {}

# --- 1. bound comparison: parity only vs parity + leaf peeling ----------------------
rows = []
for keep in (136, 128):
    for idx in range(4):
        r = {}
        for name, env in (('parity', {'SNAKE_NO_PEEL': '1'}), ('peel', {})):
            res, sec = run(['regrow', 9, keep, 193, 10**11, -1, 1], [bank[idx]], env)
            r[name] = (res[0]['nodes'], sec, res[0]['status'])
        rows.append((keep, idx, r))
tab = []
for keep, idx, r in rows:
    ratio = r['parity'][0] / max(1, r['peel'][0])
    tab.append(rf"{keep} & {idx} & {sci(r['parity'][0])} & {sci(r['peel'][0])} & {ratio:.1f} & "
               rf"{r['parity'][1]:.2f} & {r['peel'][1]:.2f} & {r['peel'][2].lower()} \\")
frags['boundtable'] = '\n'.join(tab)
tot_p = sum(r['parity'][0] for _, _, r in rows); tot_l = sum(r['peel'][0] for _, _, r in rows)
macros.append(rf'\newcommand{{\PeelRatio}}{{{tot_p / tot_l:.1f}}}')

# --- 2. demonstration: optimal Q5 snake from vertex 0 --------------------------------
res, _ = run(['regrow', 5, 1, 14, 10**9, -1, 1], [[0]])
q5 = [r for r in res if r['event'] == 'record'][0]['path']
macros.append(rf"\newcommand{{\QfiveSnake}}{{{', '.join(map(str, q5))}}}")
macros.append(rf"\newcommand{{\QfiveTrans}}{{{''.join(map(str, trans(q5)))}}}")

# --- 3. demonstration: a Q9 window with two fillings ---------------------------------
example = None
for idx in range(len(bank)):
    res, _ = run(['window', 9, 40, 8, 10, 50_000_000, 11], [bank[idx]])
    by_window = {}
    for r in res:
        if r['event'] == 'plateau':
            by_window.setdefault(tuple(r['window']), []).append(r['path'])
    for w, paths in by_window.items():
        if len(paths) == 2:
            i, j = w
            gaps = [p[i:j + 1] for p in paths]
            example = (idx, i, j, gaps)
            break
    if example:
        break
idx, i, j, gaps = example
orig = bank[idx][i:j + 1]
gaps.sort(key=lambda g: g != orig)
t0, t1 = trans(gaps[0]), trans(gaps[1])
diff = [k for k in range(len(t0)) if t0[k] != t1[k]]
macros += [rf'\newcommand{{\WinSnake}}{{{idx}}}', rf'\newcommand{{\WinI}}{{{i}}}', rf'\newcommand{{\WinJ}}{{{j}}}',
           rf'\newcommand{{\WinA}}{{{gaps[0][0]}}}', rf'\newcommand{{\WinB}}{{{gaps[0][-1]}}}']


def colour(t, d):
    return ''.join(rf'\textcolor{{accent}}{{\textbf{{{x}}}}}' if k in d else str(x) for k, x in enumerate(t))


frags['windowexample'] = (rf'\texttt{{{colour(t0, diff)}}}\\' + '\n' + rf'\texttt{{{colour(t1, diff)}}}')
macros.append(rf'\newcommand{{\WinDiff}}{{{len(diff)}}}')

# --- 4. regrowth records ---------------------------------------------------------------
reg = []
for keep in (128, 120, 112):
    d = json.loads((ROOT / 'outputs' / f'dfs_regrow_keep{keep}.json').read_text())
    nodes = [r['nodes'] for r in d['results']]
    reg.append((keep, 192 - keep, d['counts'], d['total_nodes'], statistics.median(nodes), max(nodes),
                d['elapsed_seconds'], len(nodes)))
p104 = ROOT / 'outputs' / 'dfs_regrow_keep104.partial.jsonl'
partial = [json.loads(l) for l in p104.read_text().splitlines()] if p104.exists() else []
tab, plot = [], []
for keep, freed, c, tot, med, mx, sec, n in reg:
    tab.append(rf'{keep} & {freed} & {c["INFEASIBLE"]}/{n} & {c["UNKNOWN"]} & {sci(tot)} & {sci(int(med))} & {sci(mx)} & {sec:.0f}\,s \\')
    plot.append(f'({freed},{tot / n:.4g})')
if partial:
    inf = sum(r['status'] == 'INFEASIBLE' for r in partial)
    unk = sum(r['status'] == 'UNKNOWN' for r in partial)
    nodes = [r['nodes'] for r in partial]
    tab.append(rf'104 & 88 & {inf}/{len(partial)}$^\dagger$ & {unk} & {sci(sum(nodes))} & {sci(int(statistics.median(nodes)))} & {sci(max(nodes))} & running \\')
    resolved = [r['nodes'] for r in partial if r['status'] == 'INFEASIBLE']
    if resolved:
        plot.append(f'(88,{sum(resolved) / len(resolved):.4g})')
    macros.append(rf'\newcommand{{\KeepCFourDone}}{{{len(partial)}}}')
else:
    macros.append(r'\newcommand{\KeepCFourDone}{0}')
frags['regrowtable'] = '\n'.join(tab)
macros.append(rf"\newcommand{{\regrowcoords}}{{{' '.join(plot)}}}")

# --- 5. combined moves ---------------------------------------------------------------
cb = json.loads((ROOT / 'outputs' / 'dfs_combo_s1.json').read_text())
st = cb['stats']
macros += [rf"\newcommand{{\ComboJobs}}{{{st['jobs']:,}}}".replace(',', '{,}'),
           rf"\newcommand{{\ComboWindows}}{{{st['windows']:,}}}".replace(',', '{,}'),
           rf"\newcommand{{\ComboFillings}}{{{st['fillings']:,}}}".replace(',', '{,}'),
           rf"\newcommand{{\ComboWinUnknown}}{{{st['window_unknown']:,}}}".replace(',', '{,}'),
           rf"\newcommand{{\ComboSeconds}}{{{cb['elapsed_seconds']:.0f}}}"]
wins = cb['windows']
bins = [(140, 150), (151, 160), (161, 170), (171, 180)]
tab = []
for lo, hi in bins:
    ws = [w for w in wins if lo <= w['cut'] <= hi]
    tab.append(rf"{lo}--{hi} & {len(ws)} & {sci(sum(w['alternatives'] for w in ws))} & "
               rf"{sum(w['status'] == 'EXHAUSTED' for w in ws)} & {sum(w['regrow_found'] for w in ws)} \\")
frags['combotable'] = '\n'.join(tab)

(OUT / 'macros.tex').write_text('\n'.join(macros) + '\n', encoding='utf-8')
for k, v in frags.items():
    (OUT / f'{k}.tex').write_text(v + '\n', encoding='utf-8')
print('wrote', sorted(p.name for p in OUT.glob('*.tex')))
