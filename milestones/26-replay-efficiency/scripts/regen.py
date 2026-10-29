import json, os, sys
ROOT=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
sys.path.insert(0, ROOT+'/milestones/10-window-aggregate/scripts'); sys.path.insert(0, ROOT+'/milestones/23-k6-lean/certify')
import gen_k6_core as K, gen_lean_core as GC
S=os.environ.get('STUDY', '/tmp/replay-study') + '/oleanstudy'
work, certs = S+'/work', S+'/certs'
K.register(certs); cad=K.cadical_wrapper(work)
for name in sys.argv[1:]:
    meta=json.load(open(os.path.join(K.CORE, name+'.json')))
    K.regen_cnf(meta, os.path.join(certs, name+'.cnf.gz'))
    lrat, info = GC.core_lrat(name, meta['core_ids'], work, cad, [1,2], certs, rounds=1)
    print(name, meta['variables'], info['lemmas'], info['hints'], flush=True)
