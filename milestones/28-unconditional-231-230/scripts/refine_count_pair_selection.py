"""Split only the unfinished Q012A14 selection equality, preserving its input.

Each chunk is checked by Lean rfl; a root proof checks the complete append.
The CNF, LRAT, selected IDs, RUP proof and final refutation proposition stay fixed.
"""
import ast
import json
import re
import shutil
import time
import runner as r

JOB = r.HERE/'runtime/count-pairs'
NAME = 'FastCountQ012A14'


def refine():
    source = JOB/'src'/NAME/'LocalWindow.lean'
    manifest = r.read(JOB/'manifest.json')
    item = next(x for x in manifest['cases'] if x['module'] == 'Q012A14')
    assert not item.get('selection_refinement'), 'Already refined; reuse the existing result'
    for rel, digest in item['generated_files'].items():
        assert r.digest(JOB/'src'/rel) == digest, ('Changed proof input', rel)
    old = source.read_text(encoding='utf-8')
    ids = ast.literal_eval(re.search(r'^def ids : List Nat := (.*)$', old, re.M).group(1))
    cnf_source = r.ROOT/'work/final_lean/LocalWindowCnf/Q012A14.lean'
    assert r.digest(cnf_source) == item['cnf_source_sha256']
    text = cnf_source.read_text(encoding='utf-8')
    raw = ast.literal_eval(text.split('def raw : List (List Nat) :=',1)[1].split('noncomputable def cnf',1)[0].strip())
    decoded = [[v//2 if v%2 == 0 else -(v//2) for v in row] for row in raw]
    assert len(raw) == 3156 and len(ids) == 2924 and all(0 <= i < len(raw) for i in ids)
    assert NAME+'.LocalWindow' not in r.read(r.HERE/'runtime/bridge-development/state.json')['completed']
    history = JOB/'history'/('selection-'+str(time.time_ns()))
    history.mkdir(parents=True)
    shutil.copyfile(source,history/'LocalWindow-before.lean')
    r.atomic(history/'manifest-before.json',manifest)
    build = r.HERE/'runtime/bridge-development'
    shutil.copyfile(build/'state.json',history/'development-state-before.json')
    shutil.copyfile(build/(NAME+'_LocalWindow.log'),history/'last-module.log')
    chunks = []
    for k, start in enumerate(range(0,len(ids),64)):
        label = f'Selection{k:02d}'
        part = ids[start:start+64]
        selected = [decoded[i] for i in part]
        code = ('import LocalWindowCnf.Q012A14\nimport LocalWindowSelectedClauses\n'
            'set_option maxRecDepth 200000\nset_option maxHeartbeats 0\n'
            f'namespace Snake9.LocalWindow.{NAME}.{label}\n'
            f'def indices : List Nat := {part}\n'
            f'def clauses : List (List Int) := {selected}\n'
            'theorem exact_cnf : clauses = selectedClauses Q012A14.cnf indices := by rfl\n'
            f'end Snake9.LocalWindow.{NAME}.{label}\n')
        out = source.parent/(label+'.lean')
        assert not out.exists(), ('Unexpected existing chunk',out)
        out.write_text(code,encoding='utf-8',newline='\n')
        chunks.append(dict(module=NAME+'.'+label, label=label, start=start, count=len(part)))
    imports = ''.join('import '+x['module']+'\n' for x in chunks)
    new = imports+old
    valid = 'theorem valid : ids.all (fun i => decide (i < Q012A14.cnf.length)) = true := by decide +kernel'
    assert new.count(valid) == 1
    new = new.replace(valid,
        'theorem cnf_length : Q012A14.cnf.length = 3156 := by\n'
        '  rw [Q012A14.cnf, List.length_map]\n  rfl\n'
        'theorem valid : ids.all (fun i => decide (i < Q012A14.cnf.length)) = true := by\n'
        '  rw [cnf_length]\n  decide +kernel\n#check valid')
    old_exact = f'theorem exact_cnf : {NAME}.F = selectedClauses Q012A14.cnf ids := by rfl'
    assert new.count(old_exact) == 1
    joined_clauses = ' ++ '.join(x['label']+'.clauses' for x in chunks)
    joined_indices = ' ++ '.join(x['label']+'.indices' for x in chunks)
    rewrite = ', '.join('← '+x['label']+'.exact_cnf' for x in chunks)
    exact = ('private theorem selected_append (F : List (List Int)) (xs ys : List Nat) :\n'
        '    selectedClauses F (xs ++ ys) = selectedClauses F xs ++ selectedClauses F ys := by\n'
        '  simp only [selectedClauses, List.map_append]\n'
        f'theorem exact_cnf : {NAME}.F = selectedClauses Q012A14.cnf ids := by\n'
        f'  calc\n    {NAME}.F = {joined_clauses} := by rfl\n'
        f'    _ = selectedClauses Q012A14.cnf ({joined_indices}) := by\n'
        f'      simp only [selected_append, {rewrite}]\n'
        '    _ = selectedClauses Q012A14.cnf ids := by rfl\n#check exact_cnf')
    new = new.replace(old_exact,exact)
    assert new.split('theorem unsat :',1)[1] == old.split('theorem unsat :',1)[1]
    source.write_text(new,encoding='utf-8',newline='\n')
    refinement = dict(created=r.now(),kind='64-clause equality chunks with checked append',
        history=str(history.relative_to(r.HERE)),old_root_sha256=r.digest(history/'LocalWindow-before.lean'),
        new_root_sha256=r.digest(source),cnf_source_sha256=r.digest(cnf_source),
        ids_sha256=r.hashbytes(json.dumps(ids).encode()),clauses=len(decoded),selected_clauses=len(ids),
        chunks=chunks,script_sha256=r.digest(__file__),final_refutation_source_unchanged=True,
        scope='Proof decomposition only; all new chunks and the root still require Lean checks')
    item['selection_refinement'] = refinement
    item['generated_files'] = {p.relative_to(JOB/'src').as_posix():r.digest(p) for p in source.parent.glob('*.lean')}
    r.atomic(JOB/'manifest.json',manifest)
    r.atomic(r.HERE/'data/count-pair-selection-refinement.json',refinement)
    print(json.dumps(dict(chunks=len(chunks),selected=len(ids),final_refutation_source_unchanged=True)))


if __name__ == '__main__':
    refine()
