# Checking the potential inequality by shared count prefixes

The remaining finite obligation is the same potential inequality on every
accepted graph edge:

$$P+\pi(v)\le w_e+\pi(u),\qquad e:u\to v.$$

The previous checker restarted the diagram lookup for every six-count code.
A traversal of shared prefixes can reuse the intermediate diagram state and
stop immediately on a rejecting branch. The graph, weights and potentials
are the existing ones.

## Why the traversal suffices

Each count symbol is one of $1,\ldots,6$. After a prefix has been read, the
diagram determines which next symbols can still lead to acceptance. Its
rejecting leaf stays rejecting under every further symbol. Therefore, reaching
that leaf permits all remaining completions of the prefix to be omitted.

For a branch that has not been rejected, the six possible next symbols cover
all continuations. Apply the same argument to each successor. When six symbols
have been read, an accepting leaf requires precisely the original edge
inequality. Induction on the number of unread symbols proves that successful
checks at the accepting leaves imply the inequality for every accepted code.

The integer prefix must be updated with the same encoding used by the graph.
Appending symbol $a\in\{1,\ldots,6\}$ changes an accumulated value $p$ to
$6p+a-1$. The existing digit-reconstruction theorem identifies the final value
with the original count code. Thus the traversal checks the same complete
direction, history and count keys used by the actual-snake interpretation.

## Numerical enumeration

Independent prefix enumeration reproduces all 127 accepted-code lists exactly,
using the hashes from the previous exhaustive graph audit. Across the 791
assigned contexts these lists contain 4,947,008 accepted keys.

| Direction/history | Acceptance root | Accepted codes | Rejected codes | Prefix transitions | Pointwise six-step transitions |
| --- | ---: | ---: | ---: | ---: | ---: |
| 35/0 | 2620 | 7,151 | 39,505 | 13,548 | 279,936 |
| 177/43 | 3690 | 6,598 | 40,058 | 14,202 | 279,936 |

These are operation counts from the numerical enumeration. Compiler timings
must be measured separately. The earlier complete check for the completed
profile at direction 35, history 0 reached its 300-second limit.

## Checked results

Five modules passed with 25 theorem audits. Both complete contexts transfer to
the original context checker, using the exact original weights, endpoint
functions and potential candidates. No extra hypothesis is needed for either
finite context theorem.

| Profile | Direction/history | Accepted edges | Compiler seconds |
| --- | --- | ---: | ---: |
| Completed | 35/0 | 7,151 | 121.703 |
| Conditional | 177/43 | 6,598 | 165.719 |

Each proof covers every one of the 46,656 codes in its context, with rejected
branches omitted by the checked soundness argument. Together the two contexts
contain 13,749 accepted edges. The earlier 207 accepted pilot edges lie inside
these contexts and are not additional coverage.

The old pointwise completed-context attempt and the prefix traversal with
unreduced weights both reached their 300-second limits. Those attempts remain
preserved. The successful checks also use exact context simplifications, so
the measured improvement concerns the combined implementation. The numerical
transition counts alone do not predict the compiler runtime.

## Exact weight and endpoint reductions

The history evaluator can discard every rule whose signature is not emitted
by the fixed direction/history context. Lean proves this equality for any
rule list and any count code. In particular, length-three signatures contribute
zero when the stored history has fewer than two symbols. Both selected
contexts emit no history share rule.

For the completed context $(35,0)$, Lean proves for every natural count code
$c$ that

$$w(c)=120(c\bmod6+1)+
\begin{cases}96,&c\bmod7776=7106,\\0,&\text{otherwise}.\end{cases}$$

Its source and target indices are $77760+\lfloor c/6\rfloor$ and
$1049760+(c\bmod7776)$. For the conditional context $(177,43)$, the weight is
$120(c\bmod6+1)+16$, and the indices are $1353024+\lfloor c/6\rfloor$ and
$1500768+(c\bmod7776)$. All these equalities are checked without a bound on $c$.
They simplify evaluation while retaining the original edge statement.

## Remaining work

The complete finite graph certificate remains pending for each profile. There
are 791 assigned contexts per profile, and this milestone completes one for
each. The 582 joint numerical context groups from milestone 99 still require
Lean equality and transport proofs before certificates can be reused.

The next step is to generate the constant data and emitted-rule list for each
context, prove the corresponding equalities once, and apply the checked prefix
traversal. Separate first-symbol branches can be used if a complete context
exceeds the resource limit. The original direct-evaluation sources are retained
as superseded benchmark implementations and should not be restarted blindly.

Two reference-catalogue closures remain for both global proof chains. The
conditional chain also retains the five local share floors
$(16,18,16,16,16)$, with refutation caps $(15,17,15,15,15)$. A finite potential
check does not discharge these local or reference assumptions.

The maintained interval remains $191\le a(9)\le235$ edges, with 234
conditional. The contributor upper bound retains its archived evidence and
pending independent rebuild. Existing proof objects are reused; no clean
rebuild of all dependencies is claimed. Paper revision 96 and its metadata
are unchanged; the next full revision is scheduled for milestone 106.
