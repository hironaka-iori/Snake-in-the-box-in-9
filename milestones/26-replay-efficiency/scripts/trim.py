# trim.py ROUNDS SEEDS NAME... : hints of the core LRAT with more shrinking rounds / seeds (proofs deleted)
import json, os, sys, shutil, time
ROOT=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
sys.path.insert(0, ROOT+'/milestones/10-window-aggregate/scripts'); sys.path.insert(0, ROOT+'/milestones/23-k6-lean/certify')
import gen_k6_core as K, gen_lean_core as GC
S=os.environ.get('STUDY', '/tmp/replay-study') + '/oleanstudy'
rounds, seeds = int(sys.argv[1]), list(range(1, int(sys.argv[2]) + 1))
work = S + '/work_trim'; os.makedirs(work, exist_ok=True)
K.register(S + '/certs'); cad = K.cadical_wrapper(work)
for name in sys.argv[3:]:
    meta = json.load(open(os.path.join(K.CORE, name + '.json')))
    shutil.copy(S + '/work/' + name + '.cnf', work + '/' + name + '.cnf')
    t = time.time()
    lrat, info = GC.core_lrat(name, meta['core_ids'], work, cad, seeds, S + '/certs', rounds=rounds)
    print(json.dumps(dict(name=name, rounds=rounds, seeds=len(seeds), lemmas=info['lemmas'], hints=info['hints'], sec=round(time.time() - t, 1))), flush=True)
    for f in os.listdir(work):
        if f.startswith(name): os.remove(os.path.join(work, f))
