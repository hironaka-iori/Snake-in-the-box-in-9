#!/usr/bin/env python3
"""Emit AggregateDirection<suffix>Share<N>.lean: a window-automaton chain plus a uniform empty-square
share bonus, through the chain-independent module ShareBonus.lean.

The chain (gen_lean_swar.py --start, L directions of memory, k centres, mean P/Q, start constant D)
proves  total_bound<suffix> : P m <= Q sumA a (m-1) + C  with  C = P L - Q (L - k) + D.
Its telescoped steps i = 0 .. m-L-1 use the k-centre windows j = i + L - k (directions j .. j+k,
centres j+1 .. j+k), i.e. the m - L windows j = L-k .. m-k-1.  The share premise is stated for the
chain's L-direction shapes, so L = k + 1 is required (true for K6R34C7W and K7R34C7W16).

With LB the uniform share lower bound per window, the bound is m <= N where N is the largest integer
with   coef * N + 903 k Q <= 193494 k Q + 21 k C + Q LB L,   coef = 21 k P + Q LB + 735 k Q,
equivalently   193494 k Q + 21 k C + Q LB L < coef (N + 1) + 903 k Q   (ShareBonus.share_arith).

Example (K6, the committed 231):
  python3 gen_share_wrapper.py --suffix K6R34C7W --L 7 --k 6 --lam 9/2 --D -2 --shapes 34 --lb 21 --bound 231
Example (K7):
  python3 gen_share_wrapper.py --suffix K7R34C7W16 --L 8 --k 7 --lam 89/19 --D -15 --shapes 132 --lb 27 --bound 230
"""
import argparse
import os
import sys
from fractions import Fraction


def constants(L, k, P, Q, D, LB):
    C = P * L - Q * (L - k) + D
    coef = 21 * k * P + Q * LB + 735 * k * Q
    rhs = 193494 * k * Q + 21 * k * C + Q * LB * L - 903 * k * Q
    return C, coef, rhs, rhs // coef, Fraction(rhs, coef)


def lb_needed(L, k, P, Q, D, N):
    """Smallest LB with bound <= N (None if no LB <= 10**4 suffices)."""
    for LB in range(0, 10 ** 4):
        if constants(L, k, P, Q, D, LB)[3] <= N:
            return LB
    return None


def rgs_list(n):
    """Restricted growth strings of length n (first-occurrence labels, a_0 = 0)."""
    out = []

    def go(pre, mx):
        if len(pre) == n:
            out.append(pre)
            return
        for a in range(mx + 2 if pre else 1):
            go(pre + [a], max(mx, a))
    go([], -1)
    return out


def lst(xs):
    return '[' + ', '.join(xs) + ']'


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--suffix', required=True)
    ap.add_argument('--L', type=int, required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--K', type=int, default=7, help='lump cap of the chain (symbols 1..K+1); 5 gives `sym`')
    ap.add_argument('--lam', required=True, help='chain mean P/Q, as in total_bound<suffix>')
    ap.add_argument('--D', type=int, help='start constant of the chain (C = P L - Q (L-k) + D)')
    ap.add_argument('--C', type=int, help='constant of total_bound<suffix> (instead of --D)')
    ap.add_argument('--shapes', type=int, required=True, help='number of shapes in shapes<suffix> (documentation)')
    ap.add_argument('--lb', type=int, required=True, help='uniform share lower bound per window')
    ap.add_argument('--bound', type=int, required=True, help='expected edge bound N')
    ap.add_argument('--premise', default='', help='free text naming the share certificate (doc comment)')
    ap.add_argument('--nrest', type=int,
                    help='split the shape coverage check at prefix length L - nrest (WindowAutomatonRGS); '
                         '0 = one enumeration.  Default 3 for L >= 8 (one enumeration of the 4,140 strings of '
                         'length 8 needs 2.4 GB in the kernel), else 0')
    ap.add_argument('--outdir', default='.')
    a = ap.parse_args()

    S, L, k, LB, N = a.suffix, a.L, a.k, a.lb, a.bound
    lam = Fraction(a.lam)
    P, Q = lam.numerator, lam.denominator
    if L != k + 1:
        sys.exit(f'L = {L}, k = {k}: the shape premise needs L = k + 1')
    if (a.C is None) == (a.D is None):
        sys.exit('give exactly one of --C and --D')
    D = a.D if a.D is not None else a.C - (P * L - Q * (L - k))
    C, coef, rhs, Nmax, exact = constants(L, k, P, Q, D, LB)
    if a.C is not None:
        assert C == a.C
    print(f'{S}: P/Q = {P}/{Q}, L = {L}, k = {k}, D = {D}, C = {C}, LB = {LB}')
    print(f'  {coef} m <= {rhs}  ->  m <= {float(exact):.4f}, floor {Nmax}')
    print(f'  LB for {Nmax - 1}: {lb_needed(L, k, P, Q, D, Nmax - 1)}')
    if Nmax > N:
        sys.exit(f'LB = {LB} gives only m <= {Nmax}, not {N}')
    if N < L:
        sys.exit('bound below L')
    # certificate checked by `decide` in Lean
    assert 193494 * k * Q + 21 * k * C + Q * LB * L < coef * (N + 1) + 903 * k * Q

    NS = a.K + 1
    SYM = 'sym' if NS == 6 else f'symK {NS}'

    def dpj(n):
        return lst('pathDir p j' if j == 0 else f'pathDir p (j+{j})' for j in range(n))

    def apj(n):
        return lst(f'{SYM} (countSeq p (j+{j + 1}))' for j in range(n))

    hyps = '\n'.join(f'    (hw{cc} : ∀ j, j + {cc + 1} ≤ m → wforb{S} {dpj(cc + 1)}\n      {apj(cc)} = false)'
                     for cc in range(2, k + 1))
    hw_names = ' '.join(f'hw{cc}' for cc in range(2, k + 1))
    j0 = L - k
    dirs = ', '.join('pathDir p j' if j == 0 else f'pathDir p (j+{j})' for j in range(k + 1))
    wsum = ' + '.join(f'shareSeq p (j+{c})' for c in range(1, k + 1))
    premise = f' ({a.premise})' if a.premise else ''
    nrest = a.nrest if a.nrest is not None else (3 if L >= 8 else 0)
    P_RGS = f'(!inducedFast c || (shapes{S}.map shapeCode).any (Nat.beq (shapeCode c)))'
    if nrest == 0:
        extra_import = ''
        shape_block = f"""/-- Kernel check: every restricted growth string of length {L} passing the xor-mask induced test has
its code among the codes of `shapes{S}`. -/
theorem shareRgs{S} : allRGS {L} 0 (fun c => {P_RGS}) = true := by
  decide +kernel

theorem shareCover{S} (c : List Nat) (hc : c.length = {L}) (hr : isRGS c 0 = true) :
    {P_RGS} = true :=
  allRGS_spec {L} 0 _ shareRgs{S} c hc hr
"""
    else:
        jpre = L - nrest
        assert 1 <= jpre <= 8
        pres = rgs_list(jpre)
        pre_thms = '\n'.join(
            f'theorem shareRgs{S}_p{t} : allRGS {nrest} (rgsBound {lst(map(str, q))} 0) '
            f'(fun l => shareRgsP{S} ({lst(map(str, q))} ++ l)) = true := by\n  decide +kernel'
            for t, q in enumerate(pres))
        pre_cases = '\n'.join(f'  · exact shareRgs{S}_p{t}' for t in range(len(pres)))
        extra_import = 'import WindowAutomatonRGS\n'
        shape_block = f"""/-- The coverage test: not induced (xor-mask test), or the code of a listed shape. -/
def shareRgsP{S} (c : List Nat) : Bool := {P_RGS}

/-- The {len(pres)} restricted growth strings of length {jpre}. -/
def shareRgsPre{S} : List (List Nat) := {lst(lst(map(str, q)) for q in pres)}

theorem shareRgsPre{S}_ok : shareRgsPre{S}.all (fun q => q.length == {jpre} && q.all (· < 8)) = true := by
  decide +kernel

theorem shareRgsPre{S}_cov : letN (maskOf shapeCode shareRgsPre{S} + 1)
    (fun M => allRGS {jpre} 0 (fun pre => Nat.testBit M (shapeCode pre))) = true := by
  decide +kernel

-- one kernel enumeration per prefix: the enumeration of all strings of length {L} at once keeps
-- every intermediate term until the declaration is checked
set_option Elab.async false
{pre_thms}

theorem shareRgs{S}_pres : ∀ pre, pre ∈ shareRgsPre{S} →
    allRGS {nrest} (rgsBound pre 0) (fun l => shareRgsP{S} (pre ++ l)) = true := by
  intro pre hpre
  simp only [shareRgsPre{S}, List.mem_cons, List.not_mem_nil, or_false] at hpre
  rcases hpre with {' | '.join(['rfl'] * len(pres))}
{pre_cases}

/-- Every restricted growth string of length {L} passing the xor-mask induced test has its code among
the codes of `shapes{S}` (kernel checks split at prefix length {jpre}). -/
theorem shareCover{S} (c : List Nat) (hc : c.length = {L}) (hr : isRGS c 0 = true) :
    {P_RGS} = true :=
  allRGS_of_prefixes shareRgsP{S} {jpre} {nrest} shareRgsPre{S} shareRgsPre{S}_ok shareRgsPre{S}_cov
    shareRgs{S}_pres (by decide) c (by rw [hc]) hr
"""

    out = f"""import AggregateDirection{S}Conditional
import ShareBonus
{extra_import}
/-!
# Conditional {N}: the {S} chain plus a uniform empty-square share bonus

Generated by gen_share_wrapper.py.  Chain: L = {L} directions of memory, k = {k} centres, mean {P}/{Q},
start constant D = {D}; `total_bound{S}` reads, for a snake,

    {P} m ≤ {Q} Σ_{{j=1}}^{{m-1}} α_j + {C}          (`walk{S}`, C = P L - Q (L - k) + D).

Its telescoped steps i = 0 .. m-{L + 1} use the {k}-centre windows j = i + {j0} (directions j .. j+{k}, centres
j+1 .. j+{k}): the m - {L} windows j = {j0} .. m-{k + 1}.  Share premise: for each of the {a.shapes} shapes of
`shapes{S}`, every such window of that shape has share sum (`windowShare{S}`, weights 6/3/2) at least
{LB}{premise}.  A vertex is a centre of at most {k} windows (`ShareBonus.sum_windowShareK_le`), and
`weighted_identity_bound` closes the count (`ShareBonus.upper_of_walk_and_shares`):

    {coef} m ≤ {rhs},  i.e. m ≤ {N} ({float(exact):.2f}).
-/

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton ShareBonus
noncomputable section
set_option maxHeartbeats 1600000

/-! ## 1. The walk inequality of the chain -/

theorem walk{S} {{m : Nat}} (p : Snake m) (hm : {L} ≤ m)
{hyps} :
    {P} * m ≤ {Q} * psum (fun j => countSeq p (j+1)) (m-1) + {C} := by
  obtain ⟨_, _, hpos, _, _⟩ := countSeq_facts p (by omega)
  have hpos' : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ countSeq p j := by
    intro j hj hjm
    have := hpos (j - 1) (by omega)
    simpa [show j - 1 + 1 = j by omega] using this
  have htot := total_bound{S} (pathDir p) (countSeq p) m hm hpos'
    (fun i hi => by rw [win{S}_eq]; exact snake_inducedPattern_block p i {L + 1} hi) {hw_names}
  rw [sumA_eq_psum] at htot
  exact htot

/-! ## 2. Windows -/

/-- Directions of window `j`: the {k + 1} edges from vertex `j` to vertex `j+{k + 1}` (the window of `hw{k} j`). -/
def windowDirs{S} {{m : Nat}} (p : Snake m) (j : Nat) : List Nat :=
  [{dirs}]

/-- Share sum over the {k} centres `j+1 .. j+{k}` of window `j`. -/
def windowShare{S} {{m : Nat}} (p : Snake m) (j : Nat) : Nat :=
  {wsum}

theorem windowDirs{S}_eq {{m : Nat}} (p : Snake m) (j : Nat) : windowDirs{S} p j = blockList p j {L} := rfl

theorem windowShare{S}_eq {{m : Nat}} (p : Snake m) (j : Nat) : windowShare{S} p j = windowShareK p {k} j := by
  simp only [windowShare{S}, windowShareK, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add,
    Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]

{shape_block}
theorem window_shape_mem{S} {{m : Nat}} (p : Snake m) (j : Nat) (hj : j + {L} ≤ m) :
    canon (windowDirs{S} p j) ∈ shapes{S} := by
  rw [windowDirs{S}_eq]
  exact window_shape_mem_of shapes{S} {L} (by decide) shapes{S}_ok shareCover{S} p j hj

/-! ## 3. The conditional {N} -/

/-- Conditional {N}, plain form of the share premise: every window `j` ({j0} ≤ j, j + {k + 1} ≤ m) has share
sum at least {LB}. -/
theorem upper_{N}_of_direction_windows_and_shares_all{S} {{m : Nat}} (p : Snake m)
{hyps}
    (hshare : ∀ j, {j0} ≤ j → j + {k + 1} ≤ m → {LB} ≤ windowShare{S} p j) : m ≤ {N} := by
  by_cases hm : m < {L}
  · omega
  have hwalk := walk{S} p (by omega) {hw_names}
  exact upper_of_walk_and_shares p {P} {Q} {C} {L} {k} {LB} {N} (by omega) (by decide) (by omega) hwalk
    (fun j h1 h2 => by rw [← windowShare{S}_eq]; exact hshare j (by omega) (by omega)) (by decide)

/-- **Conditional {N}-edge bound.**  Premises: the window exclusions of the {S} chain
(`hw2` .. `hw{k}`, unchanged) and, for each of the {a.shapes} {k}-centre direction shapes of the chain, that no
window of that shape has share sum at most {LB - 1}.  Neither premise is proved in Lean. -/
theorem upper_{N}_of_direction_windows_and_shares{S} {{m : Nat}} (p : Snake m)
{hyps}
    (hshare : ∀ s ∈ shapes{S}, ∀ j, {j0} ≤ j → j + {k + 1} ≤ m →
      canon (windowDirs{S} p j) = s → {LB} ≤ windowShare{S} p j) : m ≤ {N} :=
  upper_{N}_of_direction_windows_and_shares_all{S} p {hw_names}
    (fun j h1 h2 => hshare _ (window_shape_mem{S} p j h2) j h1 h2 rfl)

#print axioms walk{S}
#print axioms window_shape_mem{S}
#print axioms upper_{N}_of_direction_windows_and_shares_all{S}
#print axioms upper_{N}_of_direction_windows_and_shares{S}
end
end Snake9
"""
    path = os.path.join(a.outdir, f'AggregateDirection{S}Share{N}.lean')
    with open(path, 'w') as f:
        f.write(out)
    print('wrote', path)


if __name__ == '__main__':
    main()
