"""Export one frozen total-count refinement; no solver or Lean invocation.

--choice NAME selects data/refine-NAME.json (UNSAT_TRIMMED_NOT_REPLAYED).
--semantics-only emits the concrete CNF and its conditional semantic theorem,
without loading propagation hints, planning slots or simulating the proof.
A later full invocation may reuse those exact bytes. Existing different bytes
are never overwritten. One Total310 namespace is reserved for one choice.

Large proof mapping/export runs in a retained system temporary directory; each
published artifact is copied exclusively and hash-checked. Failure leaves the
temporary directory and an attempt record available for diagnosis.
"""
from pathlib import Path
from itertools import combinations
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
import re
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
OLD = ROOT / 'milestones/114-total-count-pressure'
GEN = ROOT / 'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts'
MODULE = 'Total310'
NAME = 'total310'
OFFSET = 2400


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def json_bytes(value):
    return (json.dumps(value, indent=2) + '\n').encode('utf-8')


def write_once(path, content):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        assert path.read_bytes() == content, ('Refusing to replace different bytes', str(path))
        return
    with path.open('xb') as stream:
        stream.write(content)


def copy_once(source, target):
    source, target = Path(source), Path(target)
    expected = sha(source)
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        assert sha(target) == expected, ('Refusing to replace different bytes', str(target))
    else:
        with source.open('rb') as src, target.open('xb') as dst:
            for block in iter(lambda: src.read(1024 * 1024), b''):
                dst.write(block)
    assert sha(target) == expected
    return expected


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def formula(path):
    rows = []
    variables = count = None
    with Path(path).open() as stream:
        for line in stream:
            if line.startswith('p '):
                _, kind, variables, count = line.split()
                assert kind == 'cnf'
            elif line.strip() and not line.startswith('c'):
                row = list(map(int, line.split()))
                assert row[-1] == 0 and 0 not in row[:-1]
                rows.append(row[:-1])
    assert len(rows) == int(count)
    assert all(0 < abs(x) <= int(variables) for row in rows for x in row)
    return int(variables), rows


def valid_cut(vertices, ball):
    selected = set(vertices)
    assert len(selected) == len(vertices) > 2 and selected <= ball
    adjacent = {v: {w for w in selected if (v ^ w).bit_count() == 1} for v in selected}
    assert all(len(row) == 2 for row in adjacent.values())
    seen = {vertices[0]}
    todo = list(seen)
    while todo:
        for vertex in adjacent[todo.pop()] - seen:
            seen.add(vertex)
            todo.append(vertex)
    assert seen == selected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--choice', required=True)
    parser.add_argument('--semantics-only', action='store_true')
    parser.add_argument('--segment-hints', type=int, default=6000)
    parser.add_argument('--group', type=int, default=4)
    args = parser.parse_args()
    assert re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]*', args.choice)
    assert args.segment_hints > 0 and args.group > 0
    record_path = HERE / 'data' / ('refine-' + args.choice + '.json')
    record = read(record_path)
    assert record['status'] == 'UNSAT_TRIMMED_NOT_REPLAYED'
    assert record['exit_code'] == 20
    meta_path = OLD / 'data/012310-total18-certificate.json'
    meta = read(meta_path)
    assert meta['status'] == 'NATIVE_SUM_CERTIFICATE_REPLAYED_LEAN_PENDING'
    assert sha(meta_path) == record['prior_certificate_sha256']
    full_path = OLD / 'work/012310-total18/full.cnf'
    trim_path = (HERE / record['trim']).resolve()
    input_path = (HERE / record['cnf']).resolve()
    assert trim_path.is_relative_to(HERE.resolve()) and input_path.is_relative_to(HERE.resolve())
    assert sha(full_path) == meta['cnf_sha256'] == record['full_cnf_sha256']
    assert sha(trim_path) == record['trim_sha256']
    assert sha(input_path) == record['cnf_sha256']
    variables, original_full = formula(full_path)
    ids = record['input_ids']
    assert len(ids) == len(set(ids)) == record['input_clauses']
    assert all(0 < i <= len(original_full) for i in ids)
    assert formula(input_path) == (variables, [original_full[i - 1] for i in ids])
    assert variables == record['variables'] == meta['variables']
    assert meta['directions'] == [0, 1, 2, 3, 1, 0]
    assert meta['window'] == [0, 1, 3, 7, 15, 13, 12]
    assert meta['bounds'] == [[0, 21]] * 5 and meta['positions'] == list(range(5))
    assert meta['sum_cap'] == 18 and len(meta['cycle_cuts']) == 8
    assert set(record['used_original_ids']) <= set(ids)

    pins = {}

    def pin(path, expected=None):
        path = Path(path)
        digest = sha(path)
        if expected is not None:
            assert digest == expected, str(path)
        key = str(path.resolve())
        assert key not in pins or pins[key] == digest
        pins[key] = digest
        return digest

    for path in [Path(__file__), record_path, meta_path, full_path, trim_path, input_path,
                 GEN / 'gen_lean_lrat.py', GEN / 'gen_lean_core.py',
                 ROOT / 'milestones/10-window-aggregate/scripts/gen_lean_sat.py',
                 ROOT / 'milestones/10-window-aggregate/scripts/wincert.py']:
        pin(path)
    pin(GEN / 'gen_lean_core.py', record['trimming_generator_sha256'])
    semantics_base = ROOT / 'milestones/112-critical-sum-refinement'
    semantics_receipt = semantics_base / 'data/SumCountSemantics112-audit.json'
    semantic_audit = read(semantics_receipt)
    assert semantic_audit['status'] == 'PASS_SUM_COUNT_SEMANTICS' and semantic_audit['exit_code'] == 0
    pin(semantics_receipt)
    pin(semantics_base / 'lean/SumCountSemantics112.lean', semantic_audit['source_sha256'])
    pin(semantics_base / 'build-sum-semantics/SumCountSemantics112.olean', semantic_audit['olean_sha256'])
    pin(semantics_base / semantic_audit['log'], semantic_audit['log_sha256'])

    selection = dict(choice=args.choice, refinement_sha256=sha(record_path),
                     original_certificate_sha256=sha(meta_path), trim_sha256=sha(trim_path),
                     module=MODULE, namespace='Snake9.LocalWindow.' + MODULE)
    selection_path = HERE / 'data/total-selection.json'
    if selection_path.exists():
        assert read(selection_path) == selection, 'Total310 is reserved for a different frozen selection.'
    final_plan_path = HERE / 'data/total-plan.json'
    if final_plan_path.exists() and not args.semantics_only:
        old_plan = read(final_plan_path)
        assert old_plan['selection'] == selection and old_plan['exporter_sha256'] == sha(Path(__file__))
        assert old_plan['segment_hints'] == args.segment_hints and old_plan['group'] == args.group
        for path, digest in old_plan['input_pins'].items():
            assert sha(Path(path)) == digest, path
        for row in old_plan['artifacts']:
            assert sha(HERE / row['path']) == row['sha256'], row['path']
        print('REUSED_VERIFIED_NATIVE_EXPORT_LEAN_PENDING', args.choice)
        return

    # Clause-only scan keeps semantics preparation independent of the large
    # propagation-hint arrays. A full export validates and simulates them later.
    active = {abs(x) for i in ids for x in original_full[i - 1]}
    last = len(ids)
    deductions = 0
    last_clause = None
    with trim_path.open() as stream:
        for line in stream:
            assert line.endswith('\n')
            head, separator, tail = line.partition(' 0')
            assert separator and tail.strip().endswith('0')
            row = list(map(int, head.split()))
            assert row[0] > last
            last, last_clause = row[0], row[1:]
            assert all(0 < abs(x) <= variables for x in last_clause)
            active.update(abs(x) for x in last_clause)
            deductions += 1
    assert deductions == record['lemmas'] and last_clause == []
    assert len(active) < OFFSET, ('Active variables do not fit audited offset2400', len(active))
    order = sorted(active) + sorted(set(range(1, variables + 1)) - active)
    rename = {v: i + 1 for i, v in enumerate(order)}
    assert sorted(rename.values()) == list(range(1, variables + 1))

    def literal(v):
        return rename[abs(v)] * (1 if v > 0 else -1)

    full = [[literal(v) for v in row] for row in original_full]
    assert max(rename[v] for v in active) < OFFSET
    sys.path.insert(0, str(ROOT / 'milestones/10-window-aggregate/scripts'))
    import gen_lean_sat as sg
    enc = sg.TaggedEncoding(meta['window'], list(map(tuple, meta['bounds'])), radius=4)
    lits = []
    for j in meta['positions']:
        i, vertex = j + 1, enc.window[j + 1]
        used = {meta['directions'][i - 1], meta['directions'][i]}
        corners = [vertex ^ (1 << a) ^ (1 << b) for a, b in combinations(range(9), 2)
                   if a not in used and b not in used]
        assert len(corners) == len(set(corners)) == 21
        lits.extend(-enc.var[v] for v in corners)
    lits.sort()
    assert len(lits) == 105 and len(set(lits)) == 84
    enc.atmost(lits, meta['sum_cap'], ('unproved_sum',))
    for cut in meta['cycle_cuts']:
        valid_cut(cut, enc.B)
        enc.add([-enc.var[v] for v in cut], ('cut',))
    assert enc.nv == variables and enc.clauses == original_full
    assert len(enc.tags) == len(original_full)
    assert enc.ctrs[-1][0] == lits and enc.ctrs[-1][1] == 18
    enc.clauses = full
    enc.meaning = {rename[k]: v for k, v in enc.meaning.items()}
    enc.var = {v: rename[k] for v, k in enc.var.items()}
    enc.ctrs = [([literal(v) for v in ls], k, kind) for ls, k, kind in enc.ctrs]

    scratch = Path(tempfile.mkdtemp(prefix='snake115-export-' + args.choice + '-'))
    print('Retained export scratch:', scratch, flush=True)
    run = str(time.time_ns())
    attempt_path = HERE / 'logs' / ('export-total-' + run + '.json')
    state = dict(status='PREPARING',choice=args.choice,semantics_only=args.semantics_only,
                 scratch=str(scratch),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 exporter_sha256=sha(Path(__file__)),input_pins=pins)

    def save_attempt():
        attempt_path.parent.mkdir(parents=True, exist_ok=True)
        attempt_path.write_bytes(json_bytes(state))

    save_attempt()
    artifacts = []

    def publish(source, target):
        digest = copy_once(source, target)
        artifacts.append(dict(path=target.relative_to(HERE).as_posix(),sha256=digest))

    try:
        write_once(selection_path, json_bytes(selection))
        renumbering = dict(active_variables=len(active),old_to_new=rename,
                           original_cnf_sha256=sha(full_path),original_proof_sha256=sha(trim_path),
                           selection=selection)
        write_once(HERE / 'data/total-renumbering.json', json_bytes(renumbering))
        generated = scratch / 'generated'
        for directory in ['LocalWindowCnf','LocalWindowSat']:
            (generated / directory).mkdir(parents=True)
        raw_body = ',\n  '.join(str([sg.code(v) for v in full[i - 1]]) for i in ids)
        cnf_source = f'''import LocalWindowDirModel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.{MODULE}
def window : List Nat := winOf {meta['directions']}
def bounds : List (Nat × Nat) := {[tuple(b) for b in meta['bounds']]}
def raw : List (List Nat) := [
  {raw_body}]
def cnf : List (List Int) := raw.map (·.map decodeLit)
end Snake9.LocalWindow.{MODULE}
'''
        (generated / 'LocalWindowCnf' / (MODULE + '.lean')).write_text(cnf_source,encoding='utf-8',newline='\n')
        terms = []
        for ls,k,kind in enc.ctrs:
            # The extra counter's kind is not used to infer an endpoint bound:
            # it is excluded from ordinary.ctrOK and uses sound_append_sum.
            kt = '.ends' if kind[0] in ['ends','unproved_sum'] else f'(.{kind[0]} {kind[1]})'
            terms.append(f'⟨{[sg.code(v) for v in ls]}, {k}, {kt}⟩')
        tags = [enc.tags[i - 1] for i in ids]
        tag_body = ',\n  '.join(', '.join(sg.lean_tag(t) for t in tags[i:i+8]) for i in range(0,len(tags),8))
        selected = [f'⟨{enc.window[j+1]}, {meta["directions"][j]}, {meta["directions"][j+1]}, 0, 21⟩'
                    for j in meta['positions']]
        sat_source = f'''import SumCountSemantics112
import LocalWindowCnf.{MODULE}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.{MODULE}
open Snake9.LocalWindow.Tags
def meaning : MT := {sg.lean_tree_terms(enc.meaning,enc.nv)}
def ordinary : List Ctr := [{', '.join(terms[:-1])}]
def extra : Ctr := {terms[-1]}
def selected : List Centre := [{', '.join(selected)}]
def tags : List Tag := [
  {tag_body}]
theorem check :
    ckAll meaning (ordinary++[extra]) window tags raw = true ∧
    ordinary.all (ctrOK meaning (centresK window bounds)) = true ∧
    extra.lits.all (baseOK meaning) = true ∧
    extra.lits.all (negP meaning) = true ∧
    (extra.lits.map (vl meaning)).Perm (selected.flatMap corners) := by decide +kernel
theorem sat (S E : Nat → Bool)
    (ax : Axioms S E window (centresOf window bounds))
    (hsum : (selected.map fun c => absentCorners S c.v c.d₁ c.d₂).sum ≤ 18) :
    ∃ τ, cnfTrue τ cnf = true := by
  obtain ⟨hc,hcs,hbase,hneg,hperm⟩ := check
  have hcs' : ordinary.all (ctrOK meaning (centresOf window bounds)) = true := by
    simpa only [centresK_eq] using hcs
  refine ⟨tau S E meaning (ordinary++[extra]), ?_⟩
  apply SumCountSemantics112.sound_append_sum meaning ordinary extra window bounds tags raw
    hc hcs' selected hneg hperm S E
  · intro i hi
    exact List.all_eq_true.mp hbase _ (getD_mem hi)
  · exact hsum
  · exact ax
#print axioms check
#print axioms sat
end Snake9.LocalWindow.{MODULE}
'''
        (generated / 'LocalWindowSat' / (MODULE + '.lean')).write_text(sat_source,encoding='utf-8',newline='\n')
        work = scratch / 'work'
        work.mkdir()
        cnf_path = work / (NAME + '.cnf')
        cnf_path.write_bytes((f'p cnf {variables} {len(full)}\n' + ''.join(' '.join(map(str,c))+' 0\n' for c in full)).encode())
        assert formula(cnf_path) == (variables,full)
        metadata_dir = scratch / 'meta'
        metadata_dir.mkdir()
        new_meta = dict(meta,module='LocalWindowCnf.'+MODULE,core_ids=ids,dirs=meta['directions'])
        (metadata_dir / (NAME + '.json')).write_bytes(json_bytes(new_meta))
        stats = None
        checker_info = None
        if not args.semantics_only:
            state['status'] = 'MAPPING_PROOF'; save_attempt()
            mapped_path = work / (NAME + '.lrat')

            def cid(i):
                return ids[i - 1] if i <= len(ids) else len(full) + i - len(ids)

            with trim_path.open() as src, mapped_path.open('x',encoding='ascii',newline='\n') as dst:
                previous = len(ids)
                count = hints = 0
                for line in src:
                    row = list(map(int,line.split()))
                    z = row.index(0,1)
                    assert row[-1] == 0 and row[0] > previous
                    assert all(0 < v < row[0] for v in row[z+1:-1])
                    dst.write(' '.join(map(str,[cid(row[0]),*map(literal,row[1:z]),0,*map(cid,row[z+1:-1]),0]))+'\n')
                    previous = row[0]; count += 1; hints += len(row[z+1:-1])
                assert row[1:z] == [] and count == record['lemmas'] and hints == record['hints']
            lr = load(GEN / 'gen_lean_lrat.py','total115_lrat')
            lemmas = lr.read_lrat(str(mapped_path))
            planned = lr.plan(ids,lemmas)
            slots = planned[3]
            bits = next((b for b in (13,14,15) if slots <= (1 << b)-1),None)
            assert bits is not None, ('No selected audited checker fits live clause slots',slots)
            checker_name = 'LratFast' + (str(bits) if bits != 13 else '')
            if bits == 13:
                receipt_path = semantics_base / 'data/Refined112.LocalWindowUnsat.Sum3142.Data0-audit.json'
                audited = read(receipt_path)
                assert audited['status'] == 'PASS_REFERENCE_RECOVERY_MODULE' and audited['exit_code'] == 0
                matches = [(ROOT / p,d) for p,d in audited['dependencies'].items() if p.endswith('/LratFast.olean')]
                assert len(matches) == 1
                checker_object,expected = matches[0]
                pin(receipt_path); pin(checker_object,expected)
            else:
                support_path = ROOT / 'milestones/87-retained-array-membership/data/RetainedPredicates-support.json'
                support = read(support_path)
                item = support['modules'][checker_name]
                pin(support_path)
                pin(Path(item['source']),item['source_sha256'])
                pin(ROOT / item['receipt'],item['receipt_sha256'])
                checker_object = Path(item['object'])
                pin(checker_object,item['object_sha256'])
            checker_info = dict(module=checker_name,bits=bits,offset=OFFSET,slots=slots,
                                object=str(checker_object),object_sha256=sha(checker_object))
            lr.set_width(bits,fast=True,off=OFFSET)
            lr.DATA_DEF = 'noncomputable def'
            lr.GROUPED = True
            # Reuse the exact parsed proof/plan rather than duplicating large
            # hint arrays when the existing exporter requests them again.
            def cached_read(path):
                assert Path(path) == mapped_path
                return lemmas
            def cached_plan(core_ids,proof):
                assert core_ids == ids and proof is lemmas
                return planned
            lr.read_lrat = cached_read
            lr.plan = cached_plan
            state.update(status='NATIVE_EXPORT_SIMULATION',checker=checker_info); save_attempt()
            stats = lr.export(NAME,str(work),args.segment_hints,args.group,args.group,True,str(generated),str(metadata_dir))
            assert stats['simulated'] is True
            assert stats['lemmas'] == record['lemmas'] and stats['hints'] == record['hints']
            assert stats['slots'] == slots

        sources = {p.relative_to(generated).as_posix()[:-5].replace('/','.'):p for p in generated.rglob('*.lean')}
        order_modules = []
        remaining = set(sources)
        while remaining:
            ready = sorted(m for m in remaining if not set(re.findall(r'^import ([\w.]+)$',sources[m].read_text(encoding='utf-8'),re.M)) & remaining)
            assert ready, 'Generated import cycle'
            order_modules.extend(ready); remaining -= set(ready)
        ports = []
        isolated = scratch / 'isolated'
        for module in order_modules:
            source = sources[module]
            original = source.read_text(encoding='utf-8')
            changed = re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.'+MODULE+r'(?:\.[A-Za-z0-9]+)?)$',r'import Refined115.\1',original,flags=re.M)
            assert re.sub(r'^import Refined115\.',r'import ',changed,flags=re.M) == original
            target = isolated / source.relative_to(generated)
            target.parent.mkdir(parents=True,exist_ok=True)
            target.write_text(changed,encoding='utf-8',newline='\n')
            publish(source,HERE / ('generated-total-'+args.choice) / source.relative_to(generated))
            destination = HERE / 'lean/Refined115' / source.relative_to(generated)
            publish(target,destination)
            ports.append(dict(original=source.relative_to(generated).as_posix(),source_sha256=sha(source),
                              isolated=destination.relative_to(HERE).as_posix(),isolated_sha256=sha(destination)))
        destination_work = HERE / 'work' / ('export-total-'+args.choice)
        publish(cnf_path,destination_work / cnf_path.name)
        publish(metadata_dir / (NAME+'.json'),HERE / 'data/total-meta' / (NAME+'.json'))
        if not args.semantics_only:
            publish(mapped_path,destination_work / mapped_path.name)
        for path,digest in pins.items():
            assert sha(Path(path)) == digest, ('Input changed during export',path)
        plan = dict(status='GENERATED_SEMANTICS_NOT_CHECKED' if args.semantics_only else 'NATIVE_EXPORT_SIMULATED_LEAN_PENDING',
                    selection=selection,modules=['Refined115.'+m for m in order_modules],ports=ports,
                    core_clauses=len(ids),active_variables=len(active),literal_occurrences=105,distinct_literals=84,
                    appended_cycle_cuts=8,selected_cycle_input_ids=[i for i in ids if i>len(full)-8],
                    segment_hints=args.segment_hints,group=args.group,checker=checker_info,generation=stats,
                    input_pins=pins,artifacts=artifacts,exporter_sha256=sha(Path(__file__)),scratch=str(scratch),
                    scope='Concrete conditional sum semantics and, in full mode, native simulated LRAT export only. Lean checking and composition with TotalGeometry114 remain pending.')
        plan_path = HERE / 'data' / ('total-semantics-plan.json' if args.semantics_only else 'total-plan.json')
        # The scratch path is evidence of this invocation. Preserve an existing
        # equivalent plan by checking its content apart from that path.
        if plan_path.exists():
            old = read(plan_path)
            assert {k:v for k,v in old.items() if k!='scratch'} == {k:v for k,v in plan.items() if k!='scratch'}
        else:
            write_once(plan_path,json_bytes(plan))
        state.update(status=plan['status'],plan=plan_path.relative_to(HERE).as_posix(),plan_sha256=sha(plan_path),
                     finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
        save_attempt()
        print(plan['status'],len(order_modules),'modules','active variables',len(active),'checker',checker_info,flush=True)
    except BaseException as exc:
        state.update(status='STOPPED',exception=repr(exc),finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
        save_attempt()
        raise


if __name__ == '__main__':
    main()
