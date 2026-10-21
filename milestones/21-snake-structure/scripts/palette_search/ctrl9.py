# Q9 control for the piece model: bank entry 0 walk + bank palette, sizes exact -> 192 SAT; sizes >= bank, one +1 -> 193 (H2 says UNSAT).
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..', '..'))
_sys.path.insert(0, _HERE)
import sys, json; sys.path.insert(0, _os.path.join(REPO, 'milestones/21-snake-structure/scripts'))
from common import load, pc
from bankwalk import quotient
from palette import bank_palette
from pmodel import run
e = load()[0]; A, B, cell, hv = bank_palette(e); seq, sizes, L, H = quotient(e, 4)
o = run(5, 4, seq, A, B, 192, tl=300, lo=sizes, hi=sizes); print('bank0 exact', {a: b for a, b in o.items() if a != 'path'}, flush=True)
o = run(5, 4, seq, A, B, 193, tl=300, lo=sizes, hi=[s + 1 for s in sizes]); print('bank0 grow', {a: b for a, b in o.items() if a != 'path'}, flush=True)
