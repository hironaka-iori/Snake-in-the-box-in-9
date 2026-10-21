"""CNF of "window (shape + counts) AND sum of empty-square shares over the centres <= B".

Extends wincert.Encoding (same ball, same variable numbering for the ball vertices, same clauses
for the window, degree, endpoint budget, alpha counts, no-4/6-cycle, optional empties= counts).

Share definition (identical to omega_oracle.OmegaModel / omega_of minus 21*alpha):
  for a centre c with path directions u1,u2, for every k not in {u1,u2} (7 values) and every
  pair {a,b} of directions different from k (28 pairs; a or b may be a path direction):
     Q = {y, y^e_a, y^e_b, y^e_a^e_b},  y = c^e_k        (the square parallel to
     P = {c, c^e_a, c^e_b, c^e_a^e_b} across direction k)
     m = number of selected vertices of P  (c itself is selected, so 1 <= m <= 3)
     t(c,Q) = 6/m  if Q contains no selected vertex, else 0           (t in {0,2,3,6})
  share(c) = sum of t(c,Q) over the 196 pairs (k,{a,b}).
Encoding of one term:  t = 2*E + g1 + 3*g3, where
  E  <-> Q empty              (exact, the same variables/clauses as Encoding's empties=)
  g1 <-> E and m <= 2         (at most one of c^e_a, c^e_b, c^e_ab selected)
  g3 <-> E and m == 1         (none of them selected)
so the term is the unary number [E, E, g1, g3, g3, g3] (bits nonincreasing).  The "<->" are
both directions when exact=True (default); with exact=False only the directions that force the
sum up are kept (E <- empty, g <- condition), which is equisatisfiable for an upper bound.

Terms whose value is fixed to 0 by the window units (Q meets the window) are left out of the
sum; a bit g1/g3 whose condition is falsified by a window vertex of P is left out likewise.

Counters for sum <= B (upward-implication only; sound for an at-most):
  'swc'  weighted sequential counter r[i][j] <- (sum of first i terms >= j), j <= B+1
  'tot'  totalizer over the unary leaves, outputs capped at B+1
  'stot' per-centre totalizer, then a sequential chain across centres (default)
"""
import os, sys
from itertools import combinations

sys.path.insert(0, os.environ.get('WINCERT_DIR', os.path.dirname(os.path.abspath(__file__))))
from wincert import Encoding, window_from_dirs  # noqa: E402


def share_terms(window):
    """Yield (centre index, centre, Q sorted tuple, P_others) in a fixed order."""
    centers = window[1:-1]
    for i, c in enumerate(centers, 1):
        used = {(c ^ window[i - 1]).bit_length() - 1, (c ^ window[i + 1]).bit_length() - 1}
        free = [d for d in range(9) if d not in used]
        for k in free:
            y = c ^ 1 << k
            for a, b in combinations([d for d in range(9) if d != k], 2):
                Q = tuple(sorted({y, y ^ 1 << a, y ^ 1 << b, y ^ 1 << a ^ 1 << b}))
                P = (c ^ 1 << a, c ^ 1 << b, c ^ 1 << a ^ 1 << b)
                yield i - 1, c, Q, P


def share_of(S, c):
    """Exact share(c) for a selected centre c of an induced path S (independent check)."""
    S = set(S)
    used = [d for d in range(9) if c ^ 1 << d in S]
    assert len(used) == 2
    tot = 0
    for k in range(9):
        if k in used:
            continue
        y = c ^ 1 << k
        for a, b in combinations([d for d in range(9) if d != k], 2):
            Q = [y, y ^ 1 << a, y ^ 1 << b, y ^ 1 << a ^ 1 << b]
            if any(w in S for w in Q):
                continue
            m = 1 + sum(w in S for w in (c ^ 1 << a, c ^ 1 << b, c ^ 1 << a ^ 1 << b))
            tot += 6 // m
    return tot


class ShareEncoding(Encoding):
    def __init__(self, window, alpha, radius, bound, ends=2, empties=None,
                 counter='stot', exact=True):
        self.bound, self.counter, self.exact = bound, counter, exact
        super().__init__(window, alpha, radius, ends, empties)

    def build(self):
        super().build()
        self.n_base = len(self.clauses)
        X, W = self.var, set(self.window)
        self.terms = []          # per term: list of (lit, weight) unary bits, plus centre index
        self.gvars = {}
        for ci, c, Q, P in share_terms(self.window):
            assert all(w in self.B for w in Q + P)
            if any(w in W for w in Q):
                continue          # Q meets the window: t = 0
            if Q not in self.esq:
                e = self.fresh(); self.esq[Q] = e
                for w in Q:
                    self.add([-e, -X[w]], 'empty->unselected')
                self.add([e] + [X[w] for w in Q], 'selected_or_empty')
            E = self.esq[Q]
            nfix = sum(w in W for w in P)
            pv = [X[w] for w in P if w not in W]
            bits = [E, E]
            if nfix <= 1:          # g1 <-> E and (at most one of P selected)
                g1 = self.fresh()
                if nfix == 1:      # condition: none of the two free ones selected
                    self.add([-E] + pv + [g1], 'g1_def')
                    if self.exact:
                        for p in pv:
                            self.add([-g1, -p], 'g1_def')
                else:
                    for p, q in combinations(pv, 2):
                        self.add([-E, p, q, g1], 'g1_def')
                    if self.exact:
                        for p, q in combinations(pv, 2):
                            self.add([-g1, -p, -q], 'g1_def')
                if self.exact:
                    self.add([-g1, E], 'g1_def')
                bits.append(g1)
            if nfix == 0:          # g3 <-> E and none of P selected
                g3 = self.fresh()
                self.add([-E] + pv + [g3], 'g3_def')
                if self.exact:
                    self.add([-g3, E], 'g3_def')
                    for p in pv:
                        self.add([-g3, -p], 'g3_def')
                bits += [g3] * 3
            self.terms.append((ci, bits))
        self.n_share = len(self.clauses)
        if self.bound is not None:
            getattr(self, 'cnt_' + self.counter)(self.bound)

    # -- counters (all only push the count up; the bound forbids output B+1) --------------
    def cnt_swc(self, B):
        """Weighted sequential counter over terms; a term contributes its unary bits."""
        cap = B + 1
        prev = {}                                 # j -> var  (prefix sum >= j)
        for ci, bits in self.terms:
            cur = {}
            def out(j):
                j = min(j, cap)
                if j not in cur:
                    cur[j] = self.fresh()
                return cur[j]
            # prefix carried over
            for j, v in prev.items():
                self.add([-v, out(j)], 'swc')
            # this term's value t >= s  <=> bits[s-1]
            for s, lit in enumerate(bits, 1):
                if s < len(bits) and bits[s] == lit:
                    continue                      # only the top of a run of equal bits
                self.add([-lit, out(s)], 'swc')
                for j, v in prev.items():
                    self.add([-lit, -v, out(j + s)], 'swc')
            prev = cur
            if cap in prev:
                self.add([-prev[cap]], 'swc_bound')
                prev.pop(cap)
        # prev[cap] already forbidden at every step

    def _merge(self, A, Bv, cap):
        """Totalizer merge of unary vectors (lists, index t-1 -> lit 'value >= t')."""
        n = min(len(A) + len(Bv), cap)
        O = [self.fresh() for _ in range(n)]
        for i in range(len(A) + 1):
            for j in range(len(Bv) + 1):
                if i + j == 0:
                    continue
                cl = []
                if i:
                    cl.append(-A[i - 1])
                if j:
                    cl.append(-Bv[j - 1])
                cl.append(O[min(i + j, cap) - 1])
                self.add(cl, 'tot')
        return O

    def _tree(self, leaves, cap):
        nodes = [l[:cap] for l in leaves]
        while len(nodes) > 1:
            nxt = []
            for i in range(0, len(nodes) - 1, 2):
                nxt.append(self._merge(nodes[i], nodes[i + 1], cap))
            if len(nodes) % 2:
                nxt.append(nodes[-1])
            nodes = nxt
        return nodes[0] if nodes else []

    def cnt_tot(self, B):
        cap = B + 1
        root = self._tree([bits for _, bits in self.terms], cap)
        if len(root) >= cap:
            self.add([-root[cap - 1]], 'tot_bound')

    def cnt_stot(self, B):
        """Totalizer per centre, then sequential merge of the centre sums."""
        cap = B + 1
        ncent = len(self.window) - 2
        acc = None
        for ci in range(ncent):
            u = self._tree([bits for c, bits in self.terms if c == ci], cap)
            acc = u if acc is None else self._merge(acc, u, cap)
            if len(acc) >= cap:
                self.add([-acc[cap - 1]], 'stot_bound')
                acc = acc[:cap - 1]

    def model_shares(self, model):
        """Per-centre share value read from a model (for validation)."""
        ncent = len(self.window) - 2
        out = [0] * ncent
        for ci, bits in self.terms:
            out[ci] += sum(1 for l in bits if model[l - 1] > 0)
        return out
