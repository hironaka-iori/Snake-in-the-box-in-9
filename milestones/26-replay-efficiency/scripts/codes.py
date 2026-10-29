# codes.py NAME... : bits per hint of alternative hint codings (lemma words only; lits/slot words unchanged)
import json, os, sys, math, collections
ROOT=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
sys.path.insert(0, ROOT+'/milestones/10-window-aggregate/scripts')
import gen_lean_lrat as G
S=os.environ.get('STUDY', '/tmp/replay-study') + '/oleanstudy'
CORE=ROOT+'/milestones/10-window-aggregate/data/lean_core_direction_k6'
G.set_width(13, True, 4000, True)
def gamma(n): return 2*n.bit_length()-1      # Elias gamma of n>=1
for name in sys.argv[1:]:
    meta=json.load(open(os.path.join(CORE,name+'.json')))
    core_ids=meta['core_ids']
    lem=G.read_lrat(os.path.join(S,'work',name+'.lrat'))
    inp, steps, last, ns = G.plan(core_ids, lem)
    h, key = G.perfect_keys(ns)
    H=sum(len(hs) for _,_,hs in steps); L=sum(len(l) for _,l,_ in steps); n=len(steps)
    other = (n*3 + L)*13      # slot word, literal words, two terminators (current coding)
    fixed = H*13
    perlem = sum(4 + len(hs)*max(1+max(s.bit_length() for s in hs), 1) for _,_,hs in steps)   # width per lemma, slot index + flag
    gam = sum(1 + gamma(s) for _,_,hs in steps for s in hs)
    nib = sum(1 + 4*math.ceil(s.bit_length()/3) for _,_,hs in steps for s in hs)
    # move-to-front over slots: hit in the last 15 -> 1+4 bits else 1+1+h bits
    mtf=[]; mbits=0
    for _,_,hs in steps:
        for s in hs:
            if s in mtf[:15]: mbits+=5; mtf.remove(s)
            else:
                mbits+=2+h
                if s in mtf: mtf.remove(s)
            mtf.insert(0,s)
    cnt=collections.Counter(s for _,_,hs in steps for s in hs)
    ent=-sum(c*math.log2(c/H) for c in cnt.values())
    print(json.dumps(dict(name=name, hints=H, h=h, other_bits_per_hint=round(other/H,2), fixed13=13,
        per_lemma_width=round(perlem/H,2), gamma_slot=round(gam/H,2), nibble_slot=round(nib/H,2), mtf15=round(mbits/H,2),
        order0_entropy=round(ent/H,2))))
