"""Export exact four-to-six-centre coverage sources, without solving CNFs."""
import argparse
import json
import re
import shutil
import time
from prepare_count_triples_table import PIN, SOURCE, EXPECTED
import runner as r

NAMES = {4: 'Four', 5: 'Five', 6: 'Six'}
COUNTS = {4: 567, 5: 9323, 6: 5974}


def prepare(refine_four=False):
    data = r.blob(PIN, SOURCE)
    assert r.hashbytes(data) == EXPECTED
    records = json.loads(data)['exclusions']
    files, groups = {}, []
    for centres, label in NAMES.items():
        rows = [(i, row) for i, row in enumerate(records) if len(row['alpha']) == centres]
        assert len(rows) == COUNTS[centres]
        name = f'CountWindow{label}231'
        namespace = 'Snake9.' + name
        header = ('set_option maxHeartbeats 0\nset_option maxRecDepth 200000\n\n'
                  f'namespace {namespace}\n'
                  'open LocalWindow DirectionWindow WindowAutomaton CountWindowBridge\n'
                  'open CountWindowTable231 CountWindowTablePrefix231\n\n')
        keys = ['(' + str(row['dirs']) + ', [' + ', '.join(f'({a},{b})' for a, b in row['alpha']) + '])'
                for _, row in rows]
        files[f'{name}/Data.lean'] = ('import CountWindowTablePrefix231\n'
            + f'/-! Exact {centres}-centre interval keys from {PIN}. -/\n'
            + header + 'def keys : List IntervalKey := [\n  ' + ',\n  '.join(keys)
            + f']\nend {namespace}\n')
        imports, lemmas = [], []
        for a in range(1, 9):
            for b in range(1, 9):
                suffix = f'P{a}{b}'
                theorem = f'prefix{a}{b}'
                files[f'{name}/{suffix}.lean'] = (f'import {name}.Data\n' + header
                    + f'theorem {theorem} : prefixCovered keys {centres+1} [{a},{b}] = true := by decide +kernel\n'
                    + f'end {namespace}\n')
                imports.append(f'import {name}.{suffix}')
                lemmas.append(theorem)
        imports = '\n'.join(imports) + '\n'
        check = (f'theorem table_checked : prefixesCovered keys {centres+1} = true := by\n'
                 + '  simp only [prefixesCovered, allPositiveSyms, allBelow, Nat.reduceAdd,\n    '
                 + ', '.join(lemmas) + ', Bool.and_self]\n')
        proof = 'CountWindowTablePrefix231.no_window table_checked h p r (by decide) hr'
        ds = ['pathDir p r'] + [f'pathDir p (r+{i})' for i in range(1, centres+1)]
        syms = [f'symK 8 (countSeq p (r+{i}))' for i in range(1, centres+1)]
        rewrites = [f'countSeq_eq_coreAlpha p (r+{i}) (by omega)' for i in range(1, centres+1)]
        rewrites += ['pathDir_eq_dir p (by omega)'] * (centres+1)
        files[name+'.lean'] = (imports + header + check
            + f'\ntheorem no_count_window (h : AllRefutedIntervals keys) {{m : Nat}} (p : Snake m)\n'
            + f'    (r : Nat) (hr : r + {centres+1} ≤ m) :\n'
            + f'    wforbK6R34C7W (dsOf p r {centres+1}) (symsK p 8 r {centres+1}) = false :=\n  {proof}\n'
            + f'\n/-- The original aggregate hw{centres} premise; concrete refutations remain explicit. -/\n'
            + f'theorem hw{centres}_of_counts (h : AllRefutedIntervals keys) {{m : Nat}} (p : Snake m) :\n'
            + f'    ∀ r, r + {centres+1} ≤ m → wforbK6R34C7W\n      [' + ', '.join(ds) + ']\n      ['
            + ', '.join(syms) + '] = false := by\n  intro r hr\n  rw [' + ',\n    '.join(rewrites)
            + ']\n  exact no_count_window h p r hr\n\n#print axioms table_checked\n#print axioms no_count_window\n'
            + f'#print axioms hw{centres}_of_counts\nend {namespace}\n')
        groups.append(dict(centres=centres, keys=len(rows), target=name,
                           prefix_shards=64,
                           original_indices=[i for i, _ in rows]))
    dest = r.HERE / 'lean'
    changed = [relative for relative, source in files.items()
               if (dest/relative).exists() and (dest/relative).read_text(encoding='utf-8') != source]
    refinement = None
    if changed:
        assert refine_four and changed == ['CountWindowFour231.lean'], ('Unexpected source changes', changed)
        old_receipt = r.read(r.HERE/'data/count-higher-table-input.json')
        for relative, digest in old_receipt['generated_files'].items():
            assert r.digest(dest/relative) == digest, ('Changed prior generated source', relative)
            if relative != 'CountWindowFour231.lean':
                assert r.hashbytes(files[relative].encode()) == digest, ('Changed table or existing shard', relative)
        old = (dest/'CountWindowFour231.lean').read_text(encoding='utf-8')
        for theorem in ['no_count_window', 'hw4_of_counts']:
            pattern = r'theorem '+theorem+r'\b([\s\S]*?) :='
            assert re.search(pattern, old).group(1) == re.search(pattern, files['CountWindowFour231.lean']).group(1)
        history = r.HERE/'runtime/count-tables/history'/('four-prefix-'+str(time.time_ns()))
        history.mkdir(parents=True)
        shutil.copyfile(dest/'CountWindowFour231.lean',history/'CountWindowFour231-before.lean')
        r.atomic(history/'input-before.json',old_receipt)
        refinement = dict(history=str(history.relative_to(r.HERE)),created=r.now(),
            kind='Four-centre monolithic coverage replaced by all 64 two-symbol prefixes',
            unchanged_data_and_other_shards=True,unchanged_final_theorem_signatures=True,
            scope='Complete prefix coverage bridge already checked; new concrete shards still require Lean')
    for relative, source in files.items():
        p = dest / relative
        p.parent.mkdir(parents=True, exist_ok=True)
        if not p.exists() or relative in changed:
            p.write_text(source, encoding='utf-8', newline='\n')
    receipt = dict(source_commit=PIN, source_path=SOURCE, source_sha256=EXPECTED,
                   groups=groups, generated_files={rel:r.digest(dest/rel) for rel in files},
                   generator_sha256=r.digest(__file__),
                   scope='Exact keys and exhaustive prefix shards; Lean checks and local refutations remain required')
    if refinement:
        receipt['proof_refinement'] = refinement
    r.atomic(r.HERE / 'data/count-higher-table-input.json', receipt)
    print('Exported', len(files), 'Lean modules for', [g['target'] for g in groups])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--refine-four', action='store_true')
    prepare(parser.parse_args().refine_four)
