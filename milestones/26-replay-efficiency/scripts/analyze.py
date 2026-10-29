# analyze.py SRCROOT MOD : per-module olean bytes split into proof lists, checkpoints, input slots, fixed
import os, re, sys, json
src, mod = sys.argv[1], sys.argv[2]
d = os.path.join(src, 'LocalWindowUnsat', mod); od = os.path.join(src, '_olean', 'LocalWindowUnsat', mod)
NUM = re.compile(r'nat_lit (0x[0-9a-fA-F]+|\d+)')
def limb(x): return 8 * ((x.bit_length() + 63) // 64)
tot = dict(proof_elems=0, proof_limb=0, cp_elems=0, cp_limb=0, slots=0, olean_data=0, olean_check=0, olean_main=0,
           n_data=0, n_check=0, proof_olean=0, cp_olean=0, slots_olean=0)
for f in os.listdir(d):
    o = os.path.join(od, f[:-5] + '.olean')
    if f.startswith('Check'):
        tot['olean_check'] += os.path.getsize(o); tot['n_check'] += 1; continue
    t = open(os.path.join(d, f)).read()
    tot['olean_data'] += os.path.getsize(o); tot['n_data'] += 1
    for blk in re.split(r'\n(?=noncomputable def )', t):
        xs = [int(v, 0) for v in NUM.findall(blk)]
        if blk.startswith('noncomputable def proof'):
            tot['proof_elems'] += len(xs); tot['proof_limb'] += sum(map(limb, xs))
        elif blk.startswith('noncomputable def cp'):
            tot['cp_elems'] += len(xs); tot['cp_limb'] += sum(map(limb, xs))
        elif blk.startswith('noncomputable def inputSlots'):
            tot['slots'] += len(xs)
tot['olean_main'] = os.path.getsize(os.path.join(src, '_olean', 'LocalWindowUnsat', mod + '.olean'))
print(json.dumps(tot))
