"""Export the checked parity-free core and simulate packed replay without Lean."""
from pathlib import Path
from collections import Counter
import ast, hashlib, importlib.util, json, re, sys, tempfile, time

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
sys.dont_write_bytecode = True
sys.path[:0] = [str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/share_packages')]
from gen_lean_sat import TaggedEncoding
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    if isinstance(value,str): value = value.encode('utf-8')
    with path.open('xb') as stream: stream.write(value)
def json_write(path,value):
    write(path,json.dumps(value,indent=2)+'\n')
def cnf(nv,clauses):
    return (f'p cnf {nv} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)).encode('ascii')
def load(path,name):
    spec = importlib.util.spec_from_file_location(name,path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def main():
    assert not (H/'data/proof-plan.json').exists()
    assert not (H/'data/selected-core-semantics.json').exists()
    assert not (H/'lean/Recovered132G').exists()
    started = time.monotonic()
    certificate = read(H/'data/native-certificate.json')
    encoding = read(H/'data/encoding.json')
    ids = read(H/'work/certificate/core-ids.json')
    source = H/'work/certificate/trimmed.lrat'
    assert certificate['status'] == 'PASS_COMPLETE_NATIVE_RUP_REPLAY'
    assert certificate['replay']['every_trimmed_step_checked']
    assert sha(source) == certificate['trim_sha256']
    assert sha(H/'work/certificate/core-ids.json') == certificate['core_ids_sha256']
    assert len(ids) == 683 and (certificate['lemmas'],certificate['hints']) == (13299,554859)
    for rel,digest in certificate['source_files_sha256'].items():
        assert sha(R/rel) == digest, rel
    enc = TaggedEncoding(encoding['window'],encoding['bounds'],radius=9)
    enc.atmost(encoding['pair_literals'],9,('pair_counterexample_cap',))
    enc.add(encoding['even_endpoint_clause'],('one_even_endpoint',))
    enc.add(encoding['odd_endpoint_clause'],('one_odd_endpoint',))
    for v in encoding['forbidden_common_sphere']:
        enc.add([-(513+v)],('endpoint_not_common_two',v))
    assert cnf(enc.nv,enc.clauses) == (H/'work/base.cnf').read_bytes()
    assert enc.nv == 2426 and len(enc.clauses) == 96552
    tags = [enc.tags[i-1] for i in ids]
    assert not any(t[0] in ['one_even_endpoint','one_odd_endpoint'] for t in tags)
    units = [t[1] for t in tags if t[0] == 'endpoint_not_common_two']
    assert units == [0,10,18,34,66,130,258]
    assert all(t[0]!='endpoint_not_common_two' for t in tags[:676])
    assert all(t[0]=='endpoint_not_common_two' for t in tags[676:])
    generator = R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py'
    assert sha(generator) == '2f4b1339817194163a080468d2e404dd7d14e7c048f8fc90e0a2691b243bf384'
    lr = load(generator,'export132_lrat')
    original_lemmas = lr.read_lrat(str(source))
    active = {abs(x) for i in ids for x in enc.clauses[i-1]}
    active.update(abs(x) for _,clause,_ in original_lemmas for x in clause)
    assert len(active) == 311
    order = sorted(active)+sorted(set(range(1,enc.nv+1))-active)
    rename = {old:i+1 for i,old in enumerate(order)}
    inverse = {new:old for old,new in rename.items()}
    assert set(rename) == set(inverse) == set(range(1,enc.nv+1))
    def lit(value): return rename[abs(value)]*(1 if value>0 else -1)
    full = [[lit(x) for x in clause] for clause in enc.clauses]
    lemmas = [(cid,[lit(x) for x in clause],list(hints)) for cid,clause,hints in original_lemmas]
    assert all([inverse[abs(x)]*(1 if x>0 else -1) for x in cl] == old[1]
               and cid == old[0] and hints == old[2]
               for (cid,cl,hints),old in zip(lemmas,original_lemmas))
    assert max(abs(x) for i in ids for x in full[i-1]) <= 311
    counter_kinds = {'first','zero','mono','step','over'}
    used = {t[1] for t in tags if t[0] in counter_kinds}
    assert used == {1}
    needed = active | set(range(1,1025))
    meaning = {rename[old]:enc.meaning[old] for old in sorted(needed)}
    counters = []
    for index,(literals,upper,kind) in enumerate(enc.ctrs):
        if index in used:
            assert {abs(x) for x in literals} <= needed
            counters.append(dict(index=index,literals=[lit(x) for x in literals],original_literals=literals,upper=upper,kind=kind))
        else: counters.append(dict(index=index,dummy=True))
    assert len(counters[1]['literals']) == 42 and len(set(counters[1]['literals'])) == 37
    receipt = R/'milestones/112-critical-sum-refinement/data/Refined112.LocalWindowUnsat.Sum3142.Data0-audit.json'
    audit = read(receipt)
    matches = [(R/path,digest) for path,digest in audit['dependencies'].items() if path.endswith('/LratFast.olean')]
    assert len(matches) == 1 and audit['exit_code'] == 0
    checker,checker_digest = matches[0]
    assert sha(checker) == checker_digest
    plan = lr.plan(ids,lemmas)
    assert plan[3] == 1119 and plan[3] <= 8191
    assert max(len(clause) for _,clause,_ in lemmas) < 255
    assert max(len(hints) for _,_,hints in lemmas) < 4095
    export = H/'data/proof-export'
    export.mkdir(exist_ok=False)
    target = export/'endpoint132.lrat'
    write(target,''.join(' '.join(map(str,[cid,*clause,0,*hints,0]))+'\n' for cid,clause,hints in lemmas))
    write(export/'endpoint132.cnf',cnf(enc.nv,full))
    write(export/'selected-core.cnf',cnf(enc.nv,[full[i-1] for i in ids]))
    json_write(export/'meta/endpoint132.json',dict(module='LocalWindowCnf.Endpoint132',core_ids=ids))
    raw = [[2*abs(x)+(x<0) for x in full[i-1]] for i in ids]
    def definition(name,rows):
        return 'noncomputable def '+name+' : List (List Nat) := [\n'+',\n'.join('  '+str(row) for row in rows)+'\n]\n'
    cnf_source = '''import LocalWindowDirModel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.Endpoint132
noncomputable def window : List Nat := winOf [0,1,2,0,3,2]
noncomputable def bounds : List (Nat × Nat) := [(0,21),(0,21),(0,21),(0,21),(0,21)]
'''+definition('baseRaw',raw[:676])+definition('endpointRaw',raw[676:])+'''
noncomputable def raw : List (List Nat) := baseRaw ++ endpointRaw
noncomputable def cnf : List (List Int) := raw.map (·.map decodeLit)
end Snake9.LocalWindow.Endpoint132
'''
    cnf_path = H/'lean/Recovered132G/LocalWindowCnf/Endpoint132.lean'
    write(cnf_path,cnf_source)
    semantic = dict(status='EXPORTED_CORE_DATA_ACTUAL_SEMANTICS_PENDING',namespace='Snake9.LocalWindow.Endpoint132',
        cnf_module='Recovered132G.LocalWindowCnf.Endpoint132',unsat_module='Recovered132G.LocalWindowUnsat.Endpoint132',
        old_to_new=rename,new_to_old=inverse,meaning=meaning,counters=counters,tags=tags,core_ids=ids,
        base_tags=tags[:676],endpoint_tags=tags[676:],base_raw=raw[:676],endpoint_raw=raw[676:],
        base_core_ids=ids[:676],endpoint_core_ids=ids[676:],
        original_raw=[enc.clauses[i-1] for i in ids],renamed_signed_raw=[full[i-1] for i in ids],
        raw=raw,window=encoding['window'],bounds=encoding['bounds'],
        used_counter_indices=sorted(used),used_endpoint_units=units,parity_clauses_present=False,
        tag_counts=dict(Counter(t[0] for t in tags)),proof_active_variables=len(active),semantic_variable_meanings=len(meaning),
        proof_active_old_ids=sorted(active),counter_literal_occurrences=42,counter_distinct_literals=37,
        cnf_source_sha256=sha(cnf_path),selection_sha256=sha(H/'data/native-certificate.json'),
        source_input_sha256=sha(H/'work/base.cnf'),source_trim_sha256=sha(source),exporter_sha256=sha(Path(__file__)),
        scope='The683-clause core contains no parity clause and uses only counter1. Counter0 is dummy in the semantic table. Original clause IDs and counter-literal multiplicity are retained. The variable bijection is explicit. Actual-snake semantics and Lean replay remain pending.')
    json_write(H/'data/selected-core-semantics.json',semantic)
    lr.set_width(13,fast=True,off=2400)
    lr.DATA_DEF = 'noncomputable def'
    lr.GROUPED = True
    lr.read_lrat = lambda path:lemmas
    lr.plan = lambda core,proof:plan
    snapshots,files = {},[cnf_path]
    with tempfile.TemporaryDirectory(prefix='snake132-export-') as temporary:
        stats = lr.export('endpoint132',str(export),6000,4,4,True,temporary,str(export/'meta'))
        assert stats['simulated'] and (stats['lemmas'],stats['hints'],stats['slots']) == (13299,554859,1119)
        for path in sorted(Path(temporary).rglob('*.lean')):
            original = path.read_text(encoding='utf-8')
            relative = path.relative_to(temporary).as_posix()
            snapshots[relative] = dict(source=original,sha256=hashlib.sha256(original.encode()).hexdigest())
            changed = re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.Endpoint132(?:\.[A-Za-z0-9]+)?)$',
                r'import Recovered132G.\1',original,flags=re.M)
            suffix = '\n#print axioms Snake9.LocalWindow.Endpoint132.unsat\n' if path.name == 'Endpoint132.lean' else ''
            assert changed.replace('import Recovered132G.','import ') == original
            dest = H/'lean/Recovered132G'/relative
            write(dest,changed+suffix)
            files.append(dest)
    json_write(export/'original-generated-sources.json',snapshots)
    names = {p.relative_to(H/'lean').as_posix()[:-5].replace('/','.'):p for p in files}
    sequence,remaining = [],set(names)
    while remaining:
        ready = sorted(name for name in remaining if not set(re.findall(r'^import ([\w.]+)$',names[name].read_text(),re.M)) & remaining)
        assert ready, 'Cyclic import graph'
        sequence.extend(ready)
        remaining -= set(ready)
    all_sources = '\n'.join(path.read_text(encoding='utf-8') for path in files)
    assert not re.search(r'\b(sorry|admit|axiom)\b',all_sources)
    assert 'theorem unsat' in names['Recovered132G.LocalWindowUnsat.Endpoint132'].read_text()
    assert all(not re.search(r'^import LocalWindow(?:Cnf|Sat|Unsat)\.Endpoint132',path.read_text(),re.M) for path in files)
    parsed = []
    for name in ['baseRaw','endpointRaw']:
        body = cnf_source.split('noncomputable def '+name+' : List (List Nat) := ',1)[1].split('\nnoncomputable def',1)[0]
        parsed += ast.literal_eval(body.strip())
    assert parsed == raw and len(parsed) == 683
    pins = {p.relative_to(R).as_posix():sha(p) for p in [H/'data/native-certificate.json',H/'data/encoding.json',
        H/'work/base.cnf',source,H/'work/certificate/core-ids.json',generator,
        R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',R/'milestones/10-window-aggregate/scripts/wincert.py',Path(__file__)]}
    out = dict(status='EXPORTED_AND_SIMULATED_LEAN_REPLAY_PENDING',stats=stats,module_order=sequence,
        artifacts=[dict(path=p.relative_to(H).as_posix(),sha256=sha(p)) for p in files],
        export_receipts=[dict(path=p.relative_to(H).as_posix(),sha256=sha(p)) for p in sorted(export.rglob('*')) if p.is_file()],
        checker_module='LratFast',checker_object=str(checker),checker_object_sha256=checker_digest,
        checker_receipt=str(receipt),checker_receipt_sha256=sha(receipt),
        source_files_sha256=pins,exporter_sha256=sha(Path(__file__)),generator_sha256=sha(generator),
        semantic_data_sha256=sha(H/'data/selected-core-semantics.json'),
        original_core_ids_preserved=True,variable_renaming_bijective=True,parity_clauses_present=False,
        used_counter_indices=[1],counter_occurrences_preserved=42,original_generated_sources_retained=True,
        structural_checks=dict(imports_acyclic=True,all_internal_imports_isolated=True,raw_core_reparsed=True,
            no_sorry_admit_or_axiom_declarations=True,packed_full_replay_simulated=True),
        lean_compiler_started=False,new_native_solver_started=False,seconds=time.monotonic()-started,
        scope='Complete Python simulation of the packed selected contradiction. All generated Lean modules and the actual-snake interpretation remain pending. No parity assumption occurs in the selected core. No global bound is claimed.')
    json_write(H/'data/proof-plan.json',out)
    print(json.dumps({k:v for k,v in out.items() if k not in ['artifacts','export_receipts','source_files_sha256','module_order']},indent=2))

if __name__ == '__main__':
    main()
