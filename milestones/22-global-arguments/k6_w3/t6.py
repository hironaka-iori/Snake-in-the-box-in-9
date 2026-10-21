"""Six-centre w_3 charges T6 on given 6-window keys (exact-minimum search of w3survey.search, then the
witness descent of ceil.py), to compare T6/6 with the T5/5 per-vertex means of the same cycle.
usage: t6.py KEYSEC key ...   (key = dirs/alpha as printed by keystr, e.g. 0123014/4,3,5,3,4,6+)"""
import sys, os, json
from k6w3lib import *
from ceil import descend


def parse(s):
    d, a = s.split('/')
    al = [(6, 21) if x == '6+' else (int(x), int(x)) for x in a.split(',')]
    return survey.key(tuple(int(c) for c in d), al)


def main():
    sec = float(sys.argv[1])
    O = load_w3()
    import refine_w3 as R
    sub = R.Sub()
    for s in sys.argv[2:]:
        k = parse(s)
        fl = sum(sub.single_lb(a) for a in k[1])      # proved single-centre minima
        survey.search(k, O, min(sec, 150), sec, fl, verbose=False)
        if O.get(k)['ub'] is not None:
            descend(k, O, sec / 2)
        st = O.get(k)
        print(s, 'lb', st['lb'], 'ub', st['ub'], 'excl', st['excl'], 'per centre', st['ub'] and st['ub'] / 6,
              'rss', round(rss_mb()), flush=True)


if __name__ == '__main__':
    main()
