"""Copy the immutable153 pilot and prepare execution scripts without Lean."""
from pathlib import Path
import ast, hashlib, json

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
P = R / 'milestones/153-pair-conditioned-share17/replay'
T = R / 'milestones/151-countfree-replay-pilot/scripts'
read = lambda p: json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def put(p, content):
    p.parent.mkdir(parents=True, exist_ok=True)
    raw = content.encode('utf-8') if isinstance(content, str) else content
    if p.exists():
        assert p.read_bytes() == raw, p
    else:
        p.write_bytes(raw)

def replace_once(s, old, new):
    assert s.count(old) == 1, (old, s.count(old))
    return s.replace(old, new)

plan = read(P / 'data/pilot-source-plan.json')
assert plan['status'] == 'SOURCE_PREPARED_UNCHECKED'
assert len(plan['module_order']) == plan['module_count'] == 34
assert (plan['pilot_deductions'], plan['pilot_hints'], plan['initial_subtrees']) == (2095, 6002, 93)
assert plan['cnf_dependency'] == 'LocalWindowCnf.ShareWindow153'
original_pins = {}
for row in plan['artifacts']:
    original = P / row['path']
    assert sha(original) == row['sha256'] and original.stat().st_size == row['bytes']
    original_pins[original.relative_to(R).as_posix()] = row['sha256']
    put(H / row['path'], original.read_bytes())
for p, digest in plan['copied_source_pins'].items():
    assert sha(R / p) == digest, p
put(H / 'data/pilot-source-plan.json', (P / 'data/pilot-source-plan.json').read_bytes())

# Preserve the established checker shape, including standard-axiom reports,
# temporary-object promotion only on success, and all dependency hashes.
checker = (T / 'check_replay.py').read_text(encoding='utf-8')
checker = checker.replace("P=R/'milestones/150-actual-pair-share'", "P=R/'milestones/154-share17-broader-semantics'")
checker = replace_once(checker,
    "B=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')",
    "B=Path(os.environ.get('SNAKE_LEAN_BIN', 'D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')).resolve()")
checker = checker.replace("[A-Za-z][A-Za-z0-9.]*", "[A-Za-z][A-Za-z0-9._]*")
checker = replace_once(checker,
    "assert a.module in expected and sha(src)==expected[a.module]",
    "assert a.module in expected and sha(src)==expected[a.module]\n"
    "prep_path=H/'data/preparation.json';prep=read(prep_path)\n"
    "assert prep['status']=='PREPARED_IMMUTABLE_PILOT_EXECUTION_UNCHECKED'\n"
    "assert sha(planpath)==prep['pilot_plan_sha256']\n"
    "assert sha(Path(__file__))==prep['execution_scripts_sha256']['scripts/check_replay.py']\n"
    "for p,d in prep['original_source_pins'].items():assert sha(R/p)==d,p")
resources_start = checker.index('def resources():')
resources_stop = checker.index("gate=resources();", resources_start)
resources_function = checker[resources_start:resources_stop]
checker = checker[:resources_start] + checker[resources_stop:]
checker = replace_once(checker, 'start=time.monotonic();stamp=str(time.time_ns())',
    resources_function + "pre_gate=resources();assert pre_gate['free_bytes']>=1.5*1024**3 and len(pre_gate['processes'])==0,pre_gate\n"
    "start=time.monotonic();stamp=str(time.time_ns())")
checker = replace_once(checker,
    "deps={str(planpath):sha(planpath),str(B/'lean.exe'):sha(B/'lean.exe')}",
    "deps={str(planpath):sha(planpath),str(prep_path):sha(prep_path),str(B/'lean.exe'):sha(B/'lean.exe')}\n"
    "for p,d in prep['original_source_pins'].items():deps[str(R/p)]=d")
checker = replace_once(checker,
    "assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['olean_sha256']",
    "assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['olean_sha256']\n"
    "    assert sha(q['log'])==q['log_sha256']\n"
    "    qfolder=Path(q['log']).parent\n"
    "    assert sha(qfolder/'source.lean.txt')==q['source_sha256']\n"
    "    assert sha(qfolder/'checker.py.txt')==q['checker_sha256']\n"
    "    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])\n"
    "    if name=='LocalWindowCnf.ShareWindow153':\n"
    "        assert rp==P/'data/LocalWindowCnf.ShareWindow153-audit.json'\n"
    "        assert q['source_sha256']==prep['shared_cnf_source_sha256']\n"
    "        assert Path(q['object']).resolve()==(P/'build/LocalWindowCnf/ShareWindow153.olean').resolve()\n"
    "    assert Path(q['object']).resolve() in {Path(x).resolve() for x in direct}\n"
    "    deps[q['log']]=q['log_sha256']\n"
    "    deps[str(qfolder/'source.lean.txt')]=q['source_sha256']\n"
    "    deps[str(qfolder/'checker.py.txt')]=q['checker_sha256']")
checker = checker.replace("['LratCheck150Replay','LratFast150Replay','InputTree150Replay','ReplayTools150']",
                          "['LratCheck153Replay','LratFast153Replay','InputTree153Replay','ReplayTools153']")
checker = checker.replace('The38 pilot modules are freshly checked. The exact concrete input from150 and generic local models from147',
                          'The34 pilot modules are freshly checked. The exact shared CNF from154 and generic local models from147')
checker = replace_once(checker,
    "        if sample['free_bytes']<state['minimum_free_bytes']:stop='LOW_FREE_MEMORY'",
    "        if sample['free_bytes']<state['minimum_free_bytes']:stop='LOW_FREE_MEMORY'\n"
    "        if any(int(p['ProcessId'])!=child.pid for p in sample['processes']):stop='OTHER_LEAN_PROCESS'")
put(H / 'scripts/check_replay.py', checker)

runner = (T / 'run_replay.py').read_text(encoding='utf-8')
runner = replace_once(runner, "assert plan['status']=='SOURCE_PREPARED_UNCHECKED'",
    "assert plan['status']=='SOURCE_PREPARED_UNCHECKED'\n"
    "prep=read(H/'data/preparation.json')\n"
    "assert sha(planpath)==prep['pilot_plan_sha256']\n"
    "assert sha(Path(__file__))==prep['execution_scripts_sha256']['scripts/run_replay.py']\n"
    "assert sha(H/'scripts/check_replay.py')==prep['execution_scripts_sha256']['scripts/check_replay.py']\n"
    "for p,d in prep['original_source_pins'].items():assert sha(R/p)==d,p")
runner = replace_once(runner,
    "assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in j['axioms'])",
    "assert j['checker_sha256']==sha(H/'scripts/check_replay.py')\n"
    "    assert len(j['axioms'])==Path(j['source']).read_text(encoding='utf-8').count('#print axioms')\n"
    "    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in j['axioms'])")
put(H / 'scripts/run_replay.py', runner)

# A future emitter can read the immutable153 packed inputs and write only155.
# It must audit the accepted pilot before generating any full-replay source.
emitter = (P / 'emit_lean.py').read_text(encoding='utf-8')
emitter = replace_once(emitter, 'import prepare_replay as p',
    "import sys, subprocess\n"
    "OUT=Path(__file__).resolve().parents[1]\n"
    "ROOT=OUT.parents[1]\n"
    "sys.path.insert(0,str(ROOT/'milestones/153-pair-conditioned-share17/replay'))\n"
    "import prepare_replay as p")
emitter = replace_once(emitter, "H=p.HERE; LEAN=H/'lean'; NS='Snake9.ReplayData153'",
    "H=p.HERE; LEAN=OUT/'lean'; NS='Snake9.ReplayData153'")
emitter = replace_once(emitter,
    "    if args.full:\n        accepted=json.loads((H/'data/pilot-completion.json').read_text())\n        assert accepted['status']=='PASS_14BIT_INITIAL_TREE_AND_CHECKPOINT_PILOT'",
    "    assert args.full, 'This adaptation only generates the full replay after the pilot audit'\n"
    "    subprocess.run([sys.executable,'-B','-X','utf8',str(OUT/'scripts/finish_pilot.py'),'--verify-only'],cwd=ROOT,check=True)\n"
    "    accepted=json.loads((OUT/'data/pilot-completion.json').read_text())\n"
    "    assert accepted['status']=='PASS_14BIT_INITIAL_TREE_AND_CHECKPOINT_PILOT'\n"
    "    prep=json.loads((OUT/'data/preparation.json').read_text())\n"
    "    assert p.sha(Path(__file__))==prep['execution_scripts_sha256']['scripts/emit_full.py']\n"
    "    for path,digest in prep['input_pins'].items():assert p.sha(ROOT/path)==digest,path")
emitter = replace_once(emitter, "path.relative_to(H)", "path.relative_to(OUT)")
emitter = replace_once(emitter,
    "'full_generation_command':'python -B emit_lean.py --full --max-source-mib 256'",
    "'full_generation_command':'python -B scripts/emit_full.py --full --max-source-mib 256'")
emitter = replace_once(emitter,
    "    p.save(H/('data/full-source-plan.json' if args.full else 'data/pilot-source-plan.json'),plan)",
    "    target=OUT/'data/full-source-plan.json';assert not target.exists()\n    p.save(target,plan)")
put(H / 'scripts/emit_full.py', emitter)

native = read(P / 'data/packed-replay.json')
assert native['status'] == 'PASS_COMPLETE_RENAMED_AND_PACKED_RUP_REPLAY'
assert (native['deductions'], native['hints'], native['final_tree_key']) == (30305,1754767,4398)
for row in native['artifacts'] + native['checkpoints']:
    assert sha(P / row['path']) == row['sha256'], row['path']
scripts=['scripts/check_replay.py','scripts/run_replay.py','scripts/finish_pilot.py','scripts/emit_full.py']
for name in scripts + ['scripts/prepare.py']:
    ast.parse((H / name).read_text(encoding='utf-8'), filename=name)
inputs = [P/'data/pilot-source-plan.json', P/'data/packed-replay.json', P/'data/sizing.json',
          P/'emit_lean.py', P/'prepare_replay.py',
          R/'milestones/153-pair-conditioned-share17/lean/LocalWindowCnf/ShareWindow153.lean']
inputs += [P / x['path'] for x in native['artifacts'] + native['checkpoints']]
prep=dict(status='PREPARED_IMMUTABLE_PILOT_EXECUTION_UNCHECKED', Lean_started=False,
          checked_modules=0, pilot_modules=34, initial_subtrees=93, tree_height=14,
          pilot_deductions=2095, pilot_references=6002, complete_replay_deductions=30305,
          complete_replay_references=1754767, complete_replay_expected_modules=137,
          full_Lean_replay_complete=False, actual_snake_share17_complete=False,
          pilot_plan_sha256=sha(H/'data/pilot-source-plan.json'),
          shared_cnf_source_sha256=sha(inputs[5]),
          original_source_pins=original_pins,
          template_pins={p.relative_to(R).as_posix():sha(p) for p in [T/'check_replay.py',T/'run_replay.py',T/'finish_pilot.py']},
          input_pins={p.relative_to(R).as_posix():sha(p) for p in inputs},
          execution_scripts_sha256={name:sha(H/name) for name in scripts},
          preparation_script_sha256=sha(Path(__file__)),
          future_external_dependency='154/data/LocalWindowCnf.ShareWindow153-audit.json and matching154/build object; receipt must PASS before import',
          scope='Only source copies, prepared checker/runner/auditor, and guarded full-source emitter. No Lean, solver, or full generation was invoked.')
put(H/'data/preparation.json',json.dumps(prep,indent=2)+'\n')
print(json.dumps({k:prep[k] for k in ['status','Lean_started','checked_modules','pilot_modules','tree_height','pilot_deductions','pilot_references','pilot_plan_sha256']}))
