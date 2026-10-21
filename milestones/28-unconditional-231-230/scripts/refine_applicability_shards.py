"""Split unfinished applicability checks without changing their propositions.

The original Data module and CNF stay byte-identical. Each replacement checks
small take/drop slices and proves their concatenation is the original input in
Lean. Run only against a stopped batch, after committing this script.
"""
import argparse
import json
import math
from pathlib import Path
import shutil
import time
import applicability_batch as batch

r = batch.common


def refine(index, first, size):
    assert index in range(34) and first >= 0 and 1 <= size < 128
    held = batch.lock()
    try:
        manifest = r.read(batch.JOB / 'manifest.json')
        batch.validate(manifest)
        state = r.read(batch.JOB / 'state.json')
        assert state['status'] == 'action_required', 'Refine a stopped failed batch only'
        commit = r.git('rev-parse', 'HEAD').decode().strip()
        script = Path(__file__).resolve()
        script_rel = script.relative_to(r.ROOT).as_posix()
        assert r.blob(commit, script_rel) == script.read_bytes().replace(b'\r\n', b'\n')
        receipt = batch.JOB / 'cases' / f'{index:02d}.json'
        case = r.read(receipt)
        for rel, digest in case['generated_files'].items():
            assert r.digest(batch.SRC / rel) == digest, rel
        prefix = case['target']
        namespace = f'Snake9.LocalWindow.ParallelShare{index:02d}Applicability'
        outputs = {}
        selected = []
        header = ('set_option maxRecDepth 200000\nset_option maxHeartbeats 0\n\n'
                  f'namespace {namespace}\n'
                  'open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks '
                  'Snake9.ParallelShareClauses\n'
                  'open Snake9.ParallelShareCertificate\n\n')
        for shard in range(first, case['chunks']):
            target = f'{prefix}.Check{shard}'
            if target in state['completed']:
                continue
            relative = target.replace('.', '/') + '.lean'
            assert relative in case['generated_files']
            original = (batch.SRC / relative).read_text(encoding='utf-8')
            assert 'by decide +kernel' in original, ('Already refined', target)
            count = min(manifest['chunk_clauses'], case['clauses'] - shard * manifest['chunk_clauses'])
            pieces = math.ceil(count / size)
            if pieces <= 1:
                continue
            imports, pairs, proofs = [], [], []
            for part in range(pieces):
                child = f'{target}Part{part}'
                theorem = f'check{shard}Part{part}'
                tags = f'(tags{shard}.drop {part * size}).take {size}'
                raw = f'(raw{shard}.drop {part * size}).take {size}'
                code = (f'import {prefix}.Data\n{header}'
                        f'theorem {theorem} : checkRaw oldMeaning ctrs window terms meaning 20 '
                        f'({tags}) ({raw}) = true := by decide +kernel\n'
                        f'end {namespace}\n')
                outputs[child.replace('.', '/') + '.lean'] = code.encode()
                imports.append(f'import {child}')
                pairs.append(f'({tags}, {raw})')
                proofs.append(f'  · exact {theorem}')
            parts = f'parts{shard}Refined'
            branches = ' | '.join('rfl' for _ in pairs)
            code = ('\n'.join(imports) + '\n' + header
                    + f'def {parts} : List (List Tag × List (List Nat)) := [{", ".join(pairs)}]\n\n'
                    + f'theorem check{shard} : checkRaw oldMeaning ctrs window terms meaning 20 '
                    + f'tags{shard} raw{shard} = true := by\n'
                    + f'  have ht : {parts}.flatMap Prod.fst = tags{shard} := by rfl\n'
                    + f'  have hr : {parts}.flatMap Prod.snd = raw{shard} := by rfl\n'
                    + '  rw [← ht, ← hr]\n  apply checkRaw_flatMap\n  intro p hp\n'
                    + f'  simp only [{parts}, List.mem_cons, List.not_mem_nil, or_false] at hp\n'
                    + f'  rcases hp with {branches}\n' + '\n'.join(proofs)
                    + f'\nend {namespace}\n')
            outputs[relative] = code.encode()
            selected.append(dict(shard=shard, original_clauses=count, pieces=pieces))
        assert selected, 'No unfinished shards to refine'
        history = batch.JOB / 'history' / f'refine-{time.time_ns()}'
        history.mkdir(parents=True)
        shutil.copyfile(receipt, history / 'original-case.json')
        r.atomic(history / 'state.json', state)
        r.atomic(history / 'manifest.json', manifest)
        if state.get('latest_log') and Path(state['latest_log']).exists():
            shutil.copyfile(state['latest_log'], history / 'failed-module.log')
        for relative, data in outputs.items():
            dest = batch.SRC / relative
            if dest.exists():
                backup = history / 'original-src' / relative
                backup.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(dest, backup)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
            case['generated_files'][relative] = r.digest(dest)
        record = dict(source_commit=commit, script_sha256=r.digest(script),
                      original_receipt_sha256=r.digest(history / 'original-case.json'),
                      history=str(history), piece_size=size, shards=selected,
                      scope='Same propositions; kernel-checked slices and exact concatenation',
                      created=r.now())
        case.setdefault('proof_refinements', []).append(record)
        r.atomic(receipt, case)
        r.atomic(history / 'refinement.json', record)
        print(json.dumps(record))
    finally:
        held.close()


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--case', type=int, required=True)
    parser.add_argument('--from-shard', type=int, required=True)
    parser.add_argument('--piece-size', type=int, default=16)
    args = parser.parse_args()
    refine(args.case, args.from_shard, args.piece_size)
