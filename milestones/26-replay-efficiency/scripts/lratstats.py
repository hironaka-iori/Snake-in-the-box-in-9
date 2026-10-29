# lratstats.py NAME... : hint usefulness (unit propagation as in the checker), coding slack, entropy bound
import json, os, sys, lzma, zlib, collections
ROOT=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
sys.path.insert(0, ROOT+'/milestones/10-window-aggregate/scripts')
import gen_lean_lrat as G
S=os.environ.get('STUDY', '/tmp/replay-study') + '/oleanstudy'
CORE=ROOT+'/milestones/10-window-aggregate/data/lean_core_direction_k6'
for name in sys.argv[1:]:
    meta=json.load(open(os.path.join(CORE,name+'.json')))
    G.set_width(13, True, 4000, True)
    core=G.read_cnf_core(os.path.join(S,'work',name+'.cnf'), meta['core_ids'])
    lem=G.read_lrat(os.path.join(S,'work',name+'.lrat'))
    cls={c:l for c,l in zip(meta['core_ids'],core)}
    H=U=W=0; wasted_lem=0; lits=0
    for cid,l,hs in lem:
        a=set(-x for x in l)   # assignment falsifying the lemma
        used=0; done=False
        for i,h in enumerate(hs):
            c=cls[h]; un=[x for x in c if -x not in a]
            if any(x in a for x in un) and False: pass
            sat=any(x in a for x in c)
            if sat: continue
            if len(un)==0: used+=1; done=True; break
            if len(un)==1: a.add(un[0]); used+=1
        assert done, name
        H+=len(hs); U+=used; lits+=len(l)
        cls[cid]=l
    # coding
    used_ids=set(meta['core_ids'])
    inp, steps, last, ns = G.plan(meta['core_ids'], lem)
    h, key = G.perfect_keys(ns)
    wl = max(13, (2*4000).bit_length())   # literal word width at OFF 4000
    cur_bits = sum((3+len(l)+len(hs))*13 for _,l,hs in steps)
    alt_bits = sum((1+len(l))*13 + (len(hs)+2)*(h+1) for _,l,hs in steps)
    words=[]
    for s,l,hs in steps: words += [key[s]] + [G.bit(x)+1 for x in l] + [0] + [key[x] for x in hs] + [0]
    raw=b''.join(w.to_bytes(2,'little') for w in words)
    # hint keys: distinct per lemma, delta coding potential
    print(json.dumps(dict(name=name, lemmas=len(lem), hints=H, useful=U, useless_frac=round(1-U/H,4), lits_per_lemma=round(lits/len(lem),1),
        hints_per_lemma=round(H/len(lem),1), slots=ns, height=h, bits_per_hint_now=round(cur_bits/H,2),
        bits_per_hint_split_width=round(alt_bits/H,2), xz_bits_per_hint=round(8*len(lzma.compress(raw, preset=9))/H,2),
        zlib_bits_per_hint=round(8*len(zlib.compress(raw,9))/H,2))), flush=True)
