"""The premise of a seven-centre chain from the proved certificate sets, and the final module.

`gen_lean_automaton7.py --tag T` writes the key list of the chain, `AllRefuted7<T> =
AllRefutedList dirKeys7<T> ∧ AllRefutedList hKeys7<T>` (`LocalWindowDirKeys7<T>`).  Most of
its keys are new; the rest are keys of the sets already replayed:

  dirKeysR4b   AllRefuted237   LocalWindowDirUnsatR4b.allRefuted237
  dirKeysR4    AllRefuted236   LocalWindowDirUnsatR4.allRefuted236
  dirKeysK6    AllRefutedK6    LocalWindowDirUnsatK6.allRefutedK6

`Refuted (winOf ds) (boundsOf syms)` does not mention the number of centres, so those keys are
reused as they are (as in milestones/23-k6-lean/certify/gen_k6_core.py glue).  This script
writes:

  keys   work/final_lean/LocalWindowDirKeysK7.lean and LocalWindowDirKeysK7_P<i>.lean:
         the new keys (every key of the chain that is in none of the three sets), sorted by
         (length, directions, counts) like every other key list, in chunks of at most
         --chunk keys (k6/F8 keys first, then H9 keys; the H9 chunks are those of
         `hChunks7<T>`), in part modules of at most --keys-per-module keys (the elaborator
         keeps about 1 GB per 7,000 keys).  The premise is chunked too:
         `AllRefutedK7 = AllRefutedSrcs dirChunksK7`, so that each chunk can be certified by
         its own module.
  glue   work/final_lean/LocalWindowDirGlue7<T>.lean: `allRefuted7<T>_of_parts :
         AllRefuted237 → AllRefuted236 → AllRefutedK6 → AllRefutedK7 → AllRefuted7<T>`.  Every
         chunk of `dirChunks7<T>` and `hChunks7<T>` is checked by one `decide +kernel` of
         `mergeOK` (LocalWindowDirGlue6) against the sources `dirKeysR4b :: dirKeysR4 ::
         dirKeysK6 :: dirChunksK7`, with one source tag per key (0, 1, 2 for the old sets, 3 + c
         for chunk c of the new keys); `AllRefutedSrcs.flatten` (LocalWindowDirGlue7) combines
         the chunks.
  final  work/spectral/stronger/UpperBound<N>.lean: `upper_bound_<N>` and
         `verified_interval_191_<N>` from `upper_<N>_of_refuted7<T>` (gen_lean_chain7.py) and the
         glue applied to `allRefuted237`, `allRefuted236`, `allRefutedK6` and `allRefutedK7`.
         `allRefutedK7 : AllRefutedK7` is the theorem of the module `LocalWindowDirUnsatK7`,
         which the certificate pipeline of the new keys has to provide (not written yet).

  reuse  The same premise without the aggregates of the three old sets.  `glue` + `final`
         import `LocalWindowDirUnsatR4b`, `…R4` and `…K6`, which import every window of
         those sets.  `reuse` writes three modules that depend only on the windows of the keys
         the chain actually takes from them:
           work/final_lean/LocalWindowDirKeysReuse7<T>.lean: those keys (`dirKeysReuse7<T>_<c>`,
             sorted, chunks of at most --chunk keys), `dirKeysReuse7<T>` (their flattening) and
             `AllRefutedReuse7<T> = AllRefutedSrcs dirChunksReuse7<T>`;
           work/final_lean/LocalWindowDirUnsatReuse7<T>.lean: imports exactly
             `LocalWindowSat.W` and `LocalWindowUnsat.W` for the window module W of each such
             key (the first of the three sets that has the key; W is read from the `AllUnsat…`
             conjunction of `LocalWindowDirSatR4b`, `…R4`, `…K6`), and proves each chunk
             `allRefutedReuse7<T>_<c> : AllRefutedList dirKeysReuse7<T>_<c>` with one
             `refine ⟨Tags.refuted_of_sat W.sat W.unsat, ?_⟩` per key; then
             `allRefutedReuse7<T> : AllRefutedReuse7<T>`;
           work/final_lean/LocalWindowDirGlue7<T>Reuse.lean: `allRefuted7<T>_of_reuse :
             AllRefutedReuse7<T> → AllRefutedK7 → AllRefuted7<T>`, one kernel merge per chunk
             of the chain as in `glue`, against the sources `dirKeysReuse7<T> :: dirChunksK7`
             (tag 0 for a reused key, 1 + c for chunk c of the new keys).  It imports key lists
             only.
         All lists of these modules are `noncomputable def` (the compiled code of a key list
         is about 15 times the size of its definition in the `.olean`).
  final --reuse  `UpperBound<N>` from `allRefuted7<T>_of_reuse allRefutedReuse7<T>
         allRefutedK7` (imports `LocalWindowDirGlue7<T>Reuse` and `LocalWindowDirUnsatReuse7<T>`
         instead of the old glue and the three old aggregates).

  python gen_lean_glue7.py keys  --keys KEYS.json.gz [--out-core DIR] [--noncomputable]
  python gen_lean_glue7.py glue  --keys KEYS.json.gz --tag T [--out-core DIR]
  python gen_lean_glue7.py reuse --keys KEYS.json.gz --tag T [--out-core DIR] [--chain-core DIR]
  python gen_lean_glue7.py final --keys KEYS.json.gz --tag T --bound N [--reuse] [--out-stronger DIR]

`keys --noncomputable` writes the key lists as `noncomputable def` (same values, an `.olean`
of about 0.2 kB instead of 3 kB per key); the kernel merges and the certificate chunks only
unfold them.
"""
import argparse, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
sys.path.insert(0, HERE)
import gen_lean_automaton7 as GA       # noqa: E402

LEAN = os.path.join(ROOT, 'work', 'final_lean')
STRONGER = os.path.join(ROOT, 'work', 'spectral', 'stronger')
ME = 'milestones/25-k7-234/lean/scripts/gen_lean_glue7.py'
OLD = [('LocalWindowDirKeysR4b', 'dirKeysR4b', 'AllRefuted237', 'allRefuted237', 'LocalWindowDirUnsatR4b'),
       ('LocalWindowDirKeysR4', 'dirKeysR4', 'AllRefuted236', 'allRefuted236', 'LocalWindowDirUnsatR4'),
       ('LocalWindowDirKeysK6', 'dirKeysK6', 'AllRefutedK6', 'allRefutedK6', 'LocalWindowDirUnsatK6')]
# The Sat aggregate of each old set and its conjunction `Unsat W.cnf ∧ …`, in key order: the
# window module W of every key.
OLD_SAT = [('LocalWindowDirSatR4b', 'AllUnsat237'), ('LocalWindowDirSatR4', 'AllUnsat236'),
           ('LocalWindowDirSatK6', 'AllUnsatK6')]


def order(k):
    return (len(k[0]), k)


def lean_keys(path):
    src = open(path).read()
    return [(tuple(map(int, d.split(','))), tuple(map(int, s.split(','))))
            for d, s in re.findall(r'\(\[([\d, ]+)\], \[([\d, ]+)\]\)', src)]


def lst(c):
    return '[' + ', '.join(map(str, c)) + ']'


def split(a):
    """The keys of the chain (generator order), the three old sources, the new chunks."""
    k6, hk = GA.load_keys(a.keys)
    olds = [lean_keys(os.path.join(LEAN, m + '.lean')) for m, *_ in OLD]
    for s in olds:
        assert s == sorted(s, key=order) and len(set(s)) == len(s)
    old = set().union(*map(set, olds))
    new6 = [k for k in k6 if k not in old]
    newh = [k for k in hk if k not in old]
    assert not set(hk) & old and newh == sorted(newh, key=order)
    c = a.chunk
    chunks = [new6[i:i + c] for i in range(0, len(new6), c)] + [newh[i:i + c] for i in range(0, len(newh), c)]
    return k6, hk, olds, chunks


def keys(a):
    k6, hk, olds, chunks = split(a)
    n6 = sum(len(ch) for ch in chunks if ch and len(ch[0][0]) < 9)
    nh = sum(len(ch) for ch in chunks) - n6
    parts, cur, n = [], [], 0
    for ci, ch in enumerate(chunks):
        if cur and n + len(ch) > a.keys_per_module:
            parts.append(cur); cur, n = [], 0
        cur.append(ci); n += len(ch)
    parts.append(cur)
    out = {}
    nc = 'noncomputable ' if a.noncomputable else ''
    for pi, part in enumerate(parts):
        body = ''.join(f'{nc}def dirKeysK7_{ci} : List (List Nat × List Nat) := [\n'
                       + ',\n'.join(f'  ({lst(d)}, {lst(s)})' for d, s in chunks[ci]) + ']\n\n'
                       for ci in part)
        out[f'LocalWindowDirKeysK7_P{pi}'] = f'''import LocalWindowDirModel

/-! Part {pi} of the new window keys of the seven-centre bound (generated by `{ME}`). -/

set_option maxHeartbeats 0

namespace Snake9.LocalWindow

{body}end Snake9.LocalWindow
'''
    src = ', '.join(os.path.relpath(os.path.abspath(p), ROOT) for p in a.keys)
    out['LocalWindowDirKeysK7'] = '\n'.join(f'import LocalWindowDirKeysK7_P{pi}' for pi in range(len(parts))) + f'''
import LocalWindowDirGlue7

/-!
# The {n6 + nh} new window keys of the seven-centre bound

Generated by `{ME} keys` from {src}: the keys of the chain that are not keys
of `dirKeysR4b` (237), `dirKeysR4` (236) or `dirKeysK6` (235).  {n6} keys of 3 to 8
directions (one lumped count per interior vertex) and {nh} H9 keys (9 directions, 7 counts),
sorted by (length, directions, counts), in {len(chunks)} chunks of at most {a.chunk} keys
(`dirChunksK7`; the chunks are defined in the part modules `LocalWindowDirKeysK7_P<i>`).

The certificate of key `(ds, syms)` is `Refuted (winOf ds) (boundsOf syms)`.  The premise
`AllRefutedK7` is chunked: every chunk is all-refuted (`AllRefutedSrcs`), so each chunk can be
certified by its own module.
-/

namespace Snake9.LocalWindow

{nc}def dirChunksK7 : List (List DirKey) :=
  [{', '.join(f'dirKeysK7_{ci}' for ci in range(len(chunks)))}]

{nc}def dirKeysK7 : List DirKey := dirChunksK7.flatten

/-- The {n6 + nh} new certificate statements of the seven-centre bound, chunk by chunk. -/
def AllRefutedK7 : Prop := AllRefutedSrcs dirChunksK7

theorem AllRefutedK7.all (h : AllRefutedK7) : AllRefutedList dirKeysK7 :=
  AllRefutedSrcs.flatten h

end Snake9.LocalWindow
'''
    for m, t in out.items():
        open(os.path.join(a.out_core, m + '.lean'), 'w').write(t)
    print(f'wrote {len(out)} modules: {n6} + {nh} new keys, {len(chunks)} chunks, {len(parts)} parts', flush=True)
    return chunks


def chain_chunks(a, k6, hk):
    """The chain's own chunks, as gen_lean_automaton7.py writes them (checked against
    LocalWindowDirKeys7<T>.lean when it exists)."""
    T = a.tag
    km = os.path.join(a.chain_core or a.out_core, f'LocalWindowDirKeys7{T}.lean')
    dch, _ = GA.chunk_rows(k6, a.chain_chunk)
    hch = [hk[i:i + a.chain_chunk] for i in range(0, len(hk), a.chain_chunk)]
    if os.path.exists(km):
        src = open(km).read()
        assert f'dirKeys7{T}_{len(dch) - 1}]' in src and f'hKeys7{T}_{len(hch) - 1}]' in src, \
            f'{km}: chunk counts differ from the generator'
    return dch, hch


def fmt_tags(ts):
    return ',\n  '.join(', '.join(map(str, ts[i:i + 40])) for i in range(0, len(ts), 40))


def glue(a):
    T = a.tag
    k6, hk, olds, chunks = split(a)
    dch, hch = chain_chunks(a, k6, hk)
    pos =[{k: i for i, k in enumerate(s)} for s in olds]
    where = {}
    for ci, ch in enumerate(chunks):
        for i, k in enumerate(ch):
            where[k] = (3 + ci, i)

    def tags(ch):
        ts, last = [], {}
        for k in ch:
            j = next((j for j in range(3) if k in pos[j]), None)
            j, i = (j, pos[j][k]) if j is not None else where[k]
            assert i > last.get(j, -1), f'source {j} is not in the order of the key list'
            last[j] = i
            ts.append(j)
        return ts
    dt = [tags(ch) for ch in dch]
    ht = [tags(ch) for ch in hch]
    cnt = [sum(t.count(j) for t in dt + ht) for j in range(3)]
    cnt.append(sum(len(t) for t in dt + ht) - sum(cnt))

    decls = []
    for nm, lst_, ts in [('D', 'dirKeys7', dt), ('H', 'hKeys7', ht)]:
        for ci, t in enumerate(ts):
            decls.append(f'''def tags{nm}7{T}_{ci} : List Nat := [
  {fmt_tags(t)}]

theorem merge{nm}7{T}_{ci} : mergeOK srcs7{T} {lst_}{T}_{ci} tags{nm}7{T}_{ci} = true := by
  decide +kernel
''')

    def cons(nm, n):
        s = 'AllRefutedSrcs.nil\''
        for ci in reversed(range(n)):
            s = f'AllRefutedSrcs.cons\' (allRefuted_of_merge hs merge{nm}7{T}_{ci})\n    ({s})'
        return s
    srcs_imports = ''.join(f'import {m}\n' for m, *_ in OLD)
    text = f'''import LocalWindowDirGlue7
{srcs_imports}import LocalWindowDirKeysK7
import LocalWindowDirKeys7{T}

/-!
# The premise of the seven-centre chain `{T}` from four certificate sets

Generated by `{ME} glue --tag {T}`.  Each of the {len(k6)} + {len(hk)} keys of `dirKeys7{T}`
and `hKeys7{T}` is found in one source: {cnt[0]} in `dirKeysR4b` (the bound 237), {cnt[1]} in
`dirKeysR4` only (the bound 236), {cnt[2]} in `dirKeysK6` (the bound 235) and {cnt[3]} in the
chunks `dirChunksK7` of the new certificates.  All lists are sorted by (length, directions,
counts), so one tag per key names its source (0, 1, 2, or 3 + the chunk of `dirChunksK7`) and
`mergeOK` checks a whole chunk of the chain by one merge in the kernel: {len(dt)} chunks of
`dirChunks7{T}` and {len(ht)} of `hChunks7{T}`.
-/

namespace Snake9.LocalWindow

/-- The sources of the merges: the three replayed sets and the chunks of the new keys. -/
def srcs7{T} : List (List DirKey) := dirKeysR4b :: dirKeysR4 :: dirKeysK6 :: dirChunksK7

set_option maxRecDepth 100000
-- One kernel merge at a time: with parallel elaboration several merges are checked at once.
set_option Elab.async false

{chr(10).join(decls)}
theorem allRefuted7{T}_of_parts (h237 : AllRefuted237) (h236 : AllRefuted236)
    (hk6 : AllRefutedK6) (hk7 : AllRefutedK7) : AllRefuted7{T} := by
  have hs : AllRefutedSrcs srcs7{T} := allRefutedSrcs_four h237 h236 hk6 hk7
  have hd : AllRefutedSrcs dirChunks7{T} :=
    {cons('D', len(dt))}
  have hh : AllRefutedSrcs hChunks7{T} :=
    {cons('H', len(ht))}
  exact And.intro (AllRefutedSrcs.flatten hd) (AllRefutedSrcs.flatten hh)

end Snake9.LocalWindow

#print axioms Snake9.LocalWindow.allRefuted7{T}_of_parts
'''
    p = os.path.join(a.out_core, f'LocalWindowDirGlue7{T}.lean')
    open(p, 'w').write(text)
    print('wrote', p, 'sources', cnt, flush=True)


def old_windows():
    """The window module of every key of each old set (dicts key -> module, in OLD order), read
    from the `AllUnsat…` conjunction (`Unsat W.cnf ∧ …`, in key order) of its Sat aggregate."""
    out = []
    for (km, *_), (sm, dn) in zip(OLD, OLD_SAT):
        ks = lean_keys(os.path.join(LEAN, km + '.lean'))
        src = open(os.path.join(LEAN, sm + '.lean')).read()
        body = src.split(f'def {dn} : Prop :=', 1)[1].split('\n\n', 1)[0]
        names = re.findall(r'Unsat (\w+)\.cnf', body)
        assert len(names) == len(ks), (sm, len(names), len(ks))
        for (d, s), w in zip(ks, names):
            assert w[1:] == ''.join(map(str, d)) + 'A' + ''.join(map(str, s)), (sm, w, d, s)
        out.append(dict(zip(ks, names)))
    return out


def reuse_split(a):
    """The chain's keys, the new chunks, the reused keys (sorted, in chunks) and the window
    module of each reused key (from the first old set that has it, as the tags of `glue`)."""
    k6, hk, olds, chunks = split(a)
    wins = old_windows()
    reused = sorted((k for k in set(k6) | set(hk) if any(k in w for w in wins)), key=order)
    win = {k: next(w[k] for w in wins if k in w) for k in reused}
    c = a.chunk
    return k6, hk, chunks, [reused[i:i + c] for i in range(0, len(reused), c)], win


def reuse(a):
    T = a.tag
    k6, hk, chunks, rch, win = reuse_split(a)
    reused = [k for ch in rch for k in ch]
    nr, nnew = len(reused), sum(map(len, chunks))
    for k in reused:
        for d in ('LocalWindowSat', 'LocalWindowUnsat'):
            f = os.path.join(LEAN, d, win[k] + '.lean')
            assert os.path.exists(f), f'missing {f}'
    by = {p: sum(win[k][0] == p for k in reused) for p in 'QRK'}
    assert sum(by.values()) == nr, by
    src = ', '.join(os.path.relpath(os.path.abspath(p), ROOT) for p in a.keys)
    nc = 'noncomputable '
    out = {}

    body = ''.join(f'{nc}def dirKeysReuse7{T}_{ci} : List DirKey := [\n'
                   + ',\n'.join(f'  ({lst(d)}, {lst(s)})' for d, s in ch) + ']\n\n'
                   for ci, ch in enumerate(rch))
    out[f'LocalWindowDirKeysReuse7{T}'] = f'''import LocalWindowDirGlue7

/-!
# The {nr} keys of the seven-centre chain `{T}` that earlier certificate sets prove

Generated by `{ME} reuse --tag {T}` from {src}: the keys of
`dirKeys7{T}` and `hKeys7{T}` that are keys of `dirKeysR4b` (237), `dirKeysR4` (236) or
`dirKeysK6` (235), sorted by (length, directions, counts), in {len(rch)} chunks of at most
{a.chunk} keys (`dirChunksReuse7{T}`).  `LocalWindowDirUnsatReuse7{T}` proves them from their
window modules alone, and `LocalWindowDirGlue7{T}Reuse` merges them with the new keys
`dirChunksK7`.
-/

set_option maxHeartbeats 0

namespace Snake9.LocalWindow

{body}{nc}def dirChunksReuse7{T} : List (List DirKey) :=
  [{', '.join(f'dirKeysReuse7{T}_{ci}' for ci in range(len(rch)))}]

{nc}def dirKeysReuse7{T} : List DirKey := dirChunksReuse7{T}.flatten

/-- The {nr} reused certificate statements of the chain `{T}`, chunk by chunk. -/
def AllRefutedReuse7{T} : Prop := AllRefutedSrcs dirChunksReuse7{T}

end Snake9.LocalWindow
'''

    imports = ''.join(f'import LocalWindowSat.{win[k]}\nimport LocalWindowUnsat.{win[k]}\n' for k in reused)
    proofs = ''.join(
        f'theorem allRefutedReuse7{T}_{ci} : AllRefutedList dirKeysReuse7{T}_{ci} := by\n'
        + ''.join(f'  refine ⟨Tags.refuted_of_sat {win[k]}.sat {win[k]}.unsat, ?_⟩\n' for k in ch)
        + '  exact trivial\n\n' for ci, ch in enumerate(rch))
    term = "AllRefutedSrcs.nil'"
    for ci in reversed(range(len(rch))):
        term = f"AllRefutedSrcs.cons' allRefutedReuse7{T}_{ci}\n    ({term})"
    out[f'LocalWindowDirUnsatReuse7{T}'] = f'''import LocalWindowTags
import LocalWindowDirKeysReuse7{T}
{imports}
/-!
# The {nr} reused keys of the seven-centre chain `{T}` from their window modules

Generated by `{ME} reuse --tag {T}`.  Every key `(ds, syms)` of
`dirKeysReuse7{T}` was certified for an earlier bound by a window module `W`: the
clause-soundness theorem `W.sat` (`LocalWindowSat.W`) and the LRAT replay `W.unsat`
(`LocalWindowUnsat.W`) give `Refuted (winOf ds) (boundsOf syms)` (`Tags.refuted_of_sat`).  Here
{by['Q']} keys come from `Q…` modules (the bound 237), {by['R']} from `R…` modules (236) and
{by['K']} from `K…` modules (235); a key of several sets uses the module of the first.  Only
these {2 * nr} window modules are imported, not the aggregates `LocalWindowDirUnsatR4b`,
`LocalWindowDirUnsatR4` and `LocalWindowDirUnsatK6`.  One `refine` per key, one theorem per
chunk of `dirChunksReuse7{T}`.
-/

set_option maxRecDepth 100000

namespace Snake9.LocalWindow

{proofs}theorem allRefutedReuse7{T} : AllRefutedReuse7{T} :=
  {term}

end Snake9.LocalWindow

#print axioms Snake9.LocalWindow.allRefutedReuse7{T}
'''

    dch, hch = chain_chunks(a, k6, hk)
    pos = {k: (0, i) for i, k in enumerate(reused)}
    for ci, ch in enumerate(chunks):
        for i, k in enumerate(ch):
            pos[k] = (1 + ci, i)

    def tags(ch):
        ts, last = [], {}
        for k in ch:
            j, i = pos[k]
            assert i > last.get(j, -1), f'source {j} is not in the order of the key list'
            last[j] = i
            ts.append(j)
        return ts
    dt = [tags(ch) for ch in dch]
    ht = [tags(ch) for ch in hch]
    assert sum(t.count(0) for t in dt + ht) == nr
    assert sum(map(len, dt + ht)) == nr + nnew == len(k6) + len(hk)
    decls = []
    for nm, lst_, ts in [('D', 'dirKeys7', dt), ('H', 'hKeys7', ht)]:
        for ci, t in enumerate(ts):
            decls.append(f'''{nc}def tagsR{nm}7{T}_{ci} : List Nat := [
  {fmt_tags(t)}]

theorem mergeR{nm}7{T}_{ci} : mergeOK srcsR7{T} {lst_}{T}_{ci} tagsR{nm}7{T}_{ci} = true := by
  decide +kernel
''')

    def cons(nm, n):
        s = 'AllRefutedSrcs.nil\''
        for ci in reversed(range(n)):
            s = f'AllRefutedSrcs.cons\' (allRefuted_of_merge hs mergeR{nm}7{T}_{ci})\n    ({s})'
        return s
    out[f'LocalWindowDirGlue7{T}Reuse'] = f'''import LocalWindowDirGlue7
import LocalWindowDirKeysReuse7{T}
import LocalWindowDirKeysK7
import LocalWindowDirKeys7{T}

/-!
# The premise of the seven-centre chain `{T}` from the reused keys and the new certificates

Generated by `{ME} reuse --tag {T}`.  Each of the {len(k6)} + {len(hk)} keys of
`dirKeys7{T}` and `hKeys7{T}` is found in one source: {nr} in `dirKeysReuse7{T}` (the keys
that the certificate sets of the bounds 237, 236 and 235 prove, `LocalWindowDirUnsatReuse7{T}`)
and {nnew} in the chunks `dirChunksK7` of the new certificates.  As in `LocalWindowDirGlue7{T}`,
all lists are sorted by (length, directions, counts), one tag per key names its source (0, or
1 + the chunk of `dirChunksK7`), and `mergeOK` checks a whole chunk of the chain by one kernel
merge: {len(dt)} chunks of `dirChunks7{T}` and {len(ht)} of `hChunks7{T}`.  This module imports
key lists only.
-/

namespace Snake9.LocalWindow

/-- The sources of the merges: the reused keys and the chunks of the new keys. -/
{nc}def srcsR7{T} : List (List DirKey) := dirKeysReuse7{T} :: dirChunksK7

set_option maxRecDepth 100000
-- One kernel merge at a time: with parallel elaboration several merges are checked at once.
set_option Elab.async false

{chr(10).join(decls)}
theorem allRefuted7{T}_of_reuse (hr : AllRefutedReuse7{T}) (hk7 : AllRefutedK7) :
    AllRefuted7{T} := by
  have hs : AllRefutedSrcs srcsR7{T} := AllRefutedSrcs.cons' (AllRefutedSrcs.flatten hr) hk7
  have hd : AllRefutedSrcs dirChunks7{T} :=
    {cons('D', len(dt))}
  have hh : AllRefutedSrcs hChunks7{T} :=
    {cons('H', len(ht))}
  exact And.intro (AllRefutedSrcs.flatten hd) (AllRefutedSrcs.flatten hh)

end Snake9.LocalWindow

#print axioms Snake9.LocalWindow.allRefuted7{T}_of_reuse
'''
    for m, t in out.items():
        open(os.path.join(a.out_core, m + '.lean'), 'w').write(t)
    print(f'wrote {", ".join(out)} in {a.out_core}: {nr} reused keys {by} in {len(rch)} chunks, '
          f'{2 * nr} window imports; {len(dt)} + {len(ht)} merges', flush=True)


def final(a):
    T, N = a.tag, a.bound
    if a.reuse:
        _, _, chunks, rch, _ = reuse_split(a)
        nnew, nr = sum(map(len, chunks)), sum(map(len, rch))
        head = f'''import AggregateDirection7{T}
import LocalWindowDirGlue7{T}Reuse
import LocalWindowDirUnsatReuse7{T}
import LocalWindowDirUnsatK7

/-!
# Unconditional bound {N}

Generated by `{ME} final --reuse --tag {T} --bound {N}`.  The premise
`AllRefuted7{T}` of `upper_{N}_of_refuted7{T}` (the seven-centre automaton `{T}`,
`AggregateDirection7{T}`) is assembled by `allRefuted7{T}_of_reuse`
(`LocalWindowDirGlue7{T}Reuse`) from two sets of kernel-checked window refutations: the {nr}
keys that the certificate sets of the bounds 237, 236 and 235 prove (`allRefutedReuse7{T}`,
`LocalWindowDirUnsatReuse7{T}`, which imports only the window modules of these keys) and the
{nnew} new certificates (`allRefutedK7`, `LocalWindowDirUnsatK7`).
-/

namespace Snake9

theorem allRefuted7{T} : LocalWindow.AllRefuted7{T} :=
  LocalWindow.allRefuted7{T}_of_reuse LocalWindow.allRefutedReuse7{T}
    LocalWindow.allRefutedK7
'''
    else:
        _, _, _, chunks = split(a)
        nnew = sum(map(len, chunks))
        imports = ''.join(f'import {u}\n' for *_, u in OLD)
        old_thms = ' '.join(f'LocalWindow.{t}' for _, _, _, t, _ in OLD)
        head = f'''import AggregateDirection7{T}
import LocalWindowDirGlue7{T}
{imports}import LocalWindowDirUnsatK7

/-!
# Unconditional bound {N}

Generated by `{ME} final --tag {T} --bound {N}`.  The premise `AllRefuted7{T}` of
`upper_{N}_of_refuted7{T}` (the seven-centre automaton `{T}`, `AggregateDirection7{T}`) is
assembled by `allRefuted7{T}_of_parts` (`LocalWindowDirGlue7{T}`) from four sets of
kernel-checked window refutations: the keys of the bound 237 (`allRefuted237`), of the bound
236 (`allRefuted236`), of the bound 235 (`allRefutedK6`) and the {nnew} new certificates
(`allRefutedK7`, `LocalWindowDirUnsatK7`).
-/

namespace Snake9

theorem allRefuted7{T} : LocalWindow.AllRefuted7{T} :=
  LocalWindow.allRefuted7{T}_of_parts {old_thms}
    LocalWindow.allRefutedK7
'''
    text = head + f'''
theorem upper_bound_{N} {{m : Nat}} (p : Snake m) : m ≤ {N} :=
  upper_{N}_of_refuted7{T} allRefuted7{T} p

theorem verified_interval_191_{N} :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ {N} := by
  refine ⟨lower_bound, ?_⟩
  rintro m ⟨p⟩
  exact upper_bound_{N} p

end Snake9

#print axioms Snake9.upper_bound_{N}
#print axioms Snake9.verified_interval_191_{N}
'''
    p = os.path.join(a.out_stronger, f'UpperBound{N}.lean')
    open(p, 'w').write(text)
    print('wrote', p, flush=True)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    for name in ('keys', 'glue', 'reuse', 'final'):
        p = sub.add_parser(name)
        p.add_argument('--keys', nargs='+', required=True, help='the key files of the chain')
        p.add_argument('--chunk', type=int, default=400,
                       help='keys per chunk of dirChunksK7 (and of dirChunksReuse7<T>)')
        p.add_argument('--out-core', default=LEAN)
        if name == 'keys':
            p.add_argument('--keys-per-module', type=int, default=4000)
            p.add_argument('--noncomputable', action='store_true',
                           help='write the key lists as `noncomputable def` (smaller .olean)')
        if name in ('glue', 'reuse', 'final'):
            p.add_argument('--tag', required=True)
        if name in ('glue', 'reuse'):
            p.add_argument('--chain-chunk', type=int, default=400,
                           help='--chunk of gen_lean_automaton7.py (the chain\'s own chunks)')
            p.add_argument('--chain-core', default=None,
                           help='directory of LocalWindowDirKeys7<T>.lean (default --out-core)')
        if name == 'final':
            p.add_argument('--bound', type=int, required=True)
            p.add_argument('--reuse', action='store_true',
                           help='use LocalWindowDirGlue7<T>Reuse and LocalWindowDirUnsatReuse7<T> '
                                '(`reuse`) instead of the glue and the three old aggregates')
            p.add_argument('--out-stronger', default=STRONGER)
    a = ap.parse_args()
    {'keys': keys, 'glue': glue, 'reuse': reuse, 'final': final}[a.cmd](a)


if __name__ == '__main__':
    main()
